functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define

    %% STUDENT START:
    
    fun {HachageTransactionHash Transaction}
        (Transaction.nonce + Transaction.sender + Transaction.receiver + Transaction.value) mod 1000000
    end

    fun {HachageBlockHash Bloc}
        (Bloc.number + Bloc.previousHash + {SumTransitionsHash Bloc.transactions}) mod 1000000
    end

    fun {SumTransitionsHash Bloctransitions}
        case Bloctransitions of nil then 0
        [] H|T then {HachageTransactionHash H} + {SumTransitionsHash T}
        end
    end

    fun {Effort Transaction}
        fun {Pow2 N}
            if N == 0 then 1 else 2 * {Pow2 N-1} end
        end
        X = {Length {Int.toString Transaction.value}}
    in
        {Pow2 X} - 1
    end

    fun {ValidationTransaction Transaction State}
        fun {ValidationTransactionBasic Transaction}
            ComputedEffort = {Effort Transaction}
        in
            Transaction.nonce > 0
            andthen Transaction.hash \= 0
            andthen Transaction.hash == {HachageTransactionHash Transaction}
            andthen Transaction.value >= 0
            andthen Transaction.max_effort > 0
            andthen ComputedEffort =< Transaction.max_effort
        end

        fun {ValidationTransactionWithState Transaction State}
            Sender = {CondSelect State Transaction.sender none}
        in
            Sender \= none
            andthen Sender.balance >= Transaction.value
            andthen Transaction.nonce == Sender.nonce + 1
        end
    in
        {ValidationTransactionBasic Transaction}
        andthen {ValidationTransactionWithState Transaction State}
    end

    fun {ValidationBloc Block PreviousBlock State}
        fun {SumEffort Transactions Accumulator}
            case Transactions of nil then Accumulator
            [] H|T then {SumEffort T Accumulator + {Effort H}}
            end
        end

        Hach = {HachageBlockHash Block}
    in
        if Block.transactions == nil then
            false
        else
            (if PreviousBlock == none then
                Block.number == 0
                andthen Block.previousHash == 0
             else
                Block.number == PreviousBlock.number + 1
                andthen Block.previousHash == PreviousBlock.hash
             end)
            andthen Block.hash == Hach
            andthen {SumEffort Block.transactions 0} =< 300
        end
    end

    %% The helper function for ExectutionBlockChain
    fun {StateFromGeniesis Genesis}
        fun {Build Users Acc}
            case Users of nil then Acc
            [] Id|Rest then 
                Balance = {CondSelect Genesis Id 0}
                NewAcc = {AdjoinAt Acc Id user(balance:Balance nonce:0)}
            in 
                {Build Rest NewAcc}
            end
        end
    in
        {Build {Arity Genesis} genesis}
    end

    %% add Tx.value to receiver balance
    %% if receiver is missing, create it with balance:0 nonce:0 before crediting

    fun {CreditReceiver State Tx}
        ReceiverId = Tx.receiver
        ReceiverInfo = {CondSelect State ReceiverId none}
    in
        if ReceiverInfo == none then
            % 1) create missing receiver with balance 0, nonce 0
            State1 = {AdjoinAt State ReceiverId user(balance:0 nonce:0)}
            % 2) credit value
            Receiver1 = {CondSelect State1 ReceiverId none}
            NewReceiver = user(balance:Receiver1.balance + Tx.value
                                nonce:Receiver1.nonce)
        in
            {AdjoinAt State1 ReceiverId NewReceiver}
        else
            % receiver exists, just credit
            NewReceiver = user(balance:ReceiverInfo.balance + Tx.value
                                nonce:ReceiverInfo.nonce)
        in
            {AdjoinAt State ReceiverId NewReceiver}
        end
    end

    fun {ApplyTransaction State Tx}
        Sender = {CondSelect State Tx.sender none}
        NewSender = user(balance:Sender.balance - Tx.value nonce:Sender.nonce + 1)
        StateAfterSender = {AdjoinAt State Tx.sender NewSender}
    in
        {CreditReceiver StateAfterSender Tx}
    end

    fun {FinalizeCurrentBlock StateAcc ChainAcc PrevBlock CurrTxs CurrTmpState}
        if CurrTxs == nil then
            StateAcc#ChainAcc#PrevBlock
        else
            TxsInOrder = {List.reverse CurrTxs}
            NewBlockNumber = if PrevBlock == none then 0 else PrevBlock.number + 1 end
            NewPrevHash = if PrevBlock == none then 0 else PrevBlock.hash end
            TempBlock = block(number:NewBlockNumber previousHash:NewPrevHash transactions:TxsInOrder hash:0)
            NewHash = {HachageBlockHash TempBlock}
            NewBlock = block(number:NewBlockNumber previousHash:NewPrevHash transactions:TxsInOrder hash:NewHash)
        in
            if {ValidationBloc NewBlock PrevBlock CurrTmpState} then
                CurrTmpState#(NewBlock|ChainAcc)#NewBlock
            else
                StateAcc#ChainAcc#PrevBlock
            end
        end
    end

    fun {ExecuteBlockchainRec Transactions StateAcc ChainAcc PrevBlock CurrBlockNo CurrTxs CurrTmpState}
        case Transactions of nil then
            {FinalizeCurrentBlock StateAcc ChainAcc PrevBlock CurrTxs CurrTmpState}
        [] Tx|Rest then
            if Tx.block_number \= CurrBlockNo then
                NewCommittedState#NewChainAcc#NewPrevBlock = {FinalizeCurrentBlock StateAcc ChainAcc PrevBlock CurrTxs CurrTmpState}
            in
                {ExecuteBlockchainRec Transactions NewCommittedState NewChainAcc NewPrevBlock Tx.block_number nil NewCommittedState}
            else
                TxEffort = {Effort Tx}
                EnrichedTx = tx(
                    block_number:Tx.block_number
                    nonce:Tx.nonce
                    hash:Tx.hash
                    sender:Tx.sender
                    receiver:Tx.receiver
                    value:Tx.value
                    effort:TxEffort
                    max_effort:Tx.max_effort
                )
            in
                if {ValidationTransaction EnrichedTx CurrTmpState} then
                    NewCurrTxs = EnrichedTx|CurrTxs
                    NewCurrTmpState = {ApplyTransaction CurrTmpState EnrichedTx}
                in
                    {ExecuteBlockchainRec Rest StateAcc ChainAcc PrevBlock CurrBlockNo NewCurrTxs NewCurrTmpState}
                else
                    {ExecuteBlockchainRec Rest StateAcc ChainAcc PrevBlock CurrBlockNo CurrTxs CurrTmpState}
                end
            end
        end
    end
        



    %% Return a string representation of the secret
    fun {Decode Blockchain}

        %% Subfunction 1: Splits digits characters into pairs of integer
        fun {DigitPairs Digits}
            case Digits
            of D1|D2|T then
                {String.toInt [D1 D2]} | {DigitPairs T}
            
            else
                nil
            end
        end

        %%Subfunction 2: conversion of pairs to letters and space
        fun {NumToChar N}
            if N == 36 then 32
            else &a + (N-10)
            end
        end

        %%Subfunction 3: decode whole block 
        fun {DecodeBlock Block}
            {Map {DigitPairs {Int.toString Block.hash}}
             fun {$ X}
                 local M = X mod 37 in
                     {NumToChar if M < 10 then 36 else M end}
                 end
             end}
        end
    
    in
        %%Last step: append all blocks together
        {FoldL Blockchain 
            fun{$ Acc Block} {Append Acc {DecodeBlock Block}} end
            ""}

    end
    %% STUDENT END


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    proc {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        StateAcc = {StateFromGeniesis GenesisState}
        InitBlockNo = case Transactions of nil then 0 [] Tx|_ then Tx.block_number end
        FinalChainRev
    in
        FinalState#FinalChainRev#_ = {ExecuteBlockchainRec Transactions StateAcc nil none InitBlockNo nil StateAcc}
        FinalBlockchain = {List.reverse FinalChainRev}
    end
end
