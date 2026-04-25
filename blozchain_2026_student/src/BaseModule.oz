functor
export
    decode:Decode
    executeBlockchain:ExecuteBlockchain
define

    %% STUDENT START:
    
    declare 
    fun {HachageTransactionHash Transaction}
        (Transaction.nonce + Transaction.sender + Transaction.receiver + Transaction.value) mod (10 ** 6)
    end

    fun {HachageBlockHash Bloc}
        (Bloc.number + Bloc.previousHash + {SumTransitionsHash Bloc.transactions}) mod (10 ** 6)
    end

    fun {SumTransitionsHash Bloctransitions}
        case Bloctransitions of nil then 0
        [] H|T then {HachageTransactionHash H} + {SumTransitionsHash T}
        end
    end

    fun {Effort Transaction}
        fun {Loop I X}
            if I > X then
                0
            else
                (2 ** I) + {Loop I+1 X}
            end
        end
        X = {Length {Int.toString Transaction.value}}
        in
        {Loop 0 X-1}
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
        fun {ValidationOfAllTransactions Transactions}
            case Transactions of nil then true
            [] H|T then {ValidationTransaction H State} andthen {ValidationOfAllTransactions T}
            end
        end

        fun {SumEffort Transactions Accumulator}
            case Transactions of nil then Accumulator
            [] H|T then {SumEffort T Accumulator + {Effort H}}
            end
        end

        Hach = {HachageBlockHash Block}
        in 
            Block.transactions \\= nil
            andthen (if PreviousBlock == none then
                        Block.number == 0
                        andthen Block.previousHash == 0
                     else
                        Block.number == PreviousBlock.number + 1
                        andthen Block.previousHash == PreviousBlock.hash
                     end)
            andthen Block.hash == Hach
                andthen {SumEffort Block.transactions 0} =< 300 
    end



    %% STUDENT END

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
            if N == 36 then &\s 
            
            else &a + (N-10)

            end
        end

        %%Subfunction 3: decode whole block 
        fun {DecodeBlock Block}
            {Map {DigitPairs {Int.toString Block.hash}} %%makes the list with duo digits
            fun {$ X}
                local M = X mod 37 in %%applies the rule of the thing
                    {NumToChar if M < 10 then 36 else M end} %%numtochar that was done above on each double digit with map
                end      
            end}
        end
    
    in
        %%Last step: append all blocks together
        {FoldL Blockchain 
            fun{$ Acc Block} {Append Acc {DecodeBlock Block}} end
            ""}
    end





        %% STUDENT START:
        %% TODO
        %% STUDENT END
    end


    % This function is the starting point of the execution
    % The GenesisState and the Transactions are given as input and the function is expected to bound the FinalState and the FinalBlockchain to their respective final values.
    fun {ExecuteBlockchain GenesisState Transactions FinalState FinalBlockchain}
        %% STUDENT START:
        %% TODO
        %% STUDENT END
    end
end