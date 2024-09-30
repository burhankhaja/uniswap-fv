import "./setup/PoolManager.spec";

using V4RouterHarness as Harness;

methods {
    // envfree
    function Harness.msgSender() external returns (address) envfree;


    // summaries for unresolved calls
    unresolved external in _._ => DISPATCH [
        V4RouterHarness._
    ] default NONDET;
    function _.permit(address,IAllowanceTransfer.PermitSingle,bytes) external => NONDET;
    function _.permit(address,IAllowanceTransfer.PermitBatch,bytes) external => NONDET;
    function _.isValidSignature(bytes32, bytes memory) internal => NONDET;
    function _.isValidSignature(bytes32, bytes) external => NONDET;
    function _._call(address, bytes memory) internal => NONDET;
    function _._call(address, bytes) external => NONDET;
    function _.notifyUnsubscribe(uint256, V4RouterHarness.PositionConfig, bytes) external => NONDET;
    function _.notifyUnsubscribe(uint256, V4RouterHarness.PositionConfig memory, bytes memory) internal => NONDET;
    // likely unsound, but assumes no callback
    function _.onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes data
    ) external => NONDET; /* expects bytes4 */
}

use builtin rule sanity filtered { f -> f.contract == currentContract }


// doc: At any given point, It should be possible to do a single currency fixed output swap
rule  swapExactOutSingle__MustNotAlwaysRevert {
   env e;
   IV4Router.ExactOutputSingleParams  params;
   require params.zeroForOne;

   // swap
   swapExactOutSingle@withrevert(e, params);
    
   // there has to be a single non-reverting path
   satisfy !lastReverted, "swapping must not always revert!";
}

//--------------------------------------------------------------------------------


// doc: Exactly the given amount of input currency by a user must be swapped in fixed input type swaps for variable amount of output currency, i.e : delta(currencyIn) == IV4Router.ExactInputSingleParams.amountIn

rule singleHop_inputSwapsExchangeFixedAmountOfInputCurrency {

   env e;
   IV4Router.ExactInputSingleParams  params;
   require params.amountIn != 0; // skip open delta calculations
   require params.zeroForOne; //assume swap of c0 -> c1
   require params.poolKey.hooks != currentContract; // differentiate b/w delta's of swapper and poolhooks

   int256 delta0_before = getCurrencyDeltaExt(params.poolKey.currency0, currentContract);
   require delta0_before == 0; //assume settled delta


   swapExactInSingle(e,params);

   int256 delta0_after = getCurrencyDeltaExt(params.poolKey.currency0, currentContract);

   // -delta0 == -(amountIn), i.e ==> delta0 == amountIn
   assert delta0_after == to_mathint(-(params.amountIn)), "Exact amount of input currency must be swapped";

}



// @audit now make for the multi-input swap // maybe have length of 1 to 2 for pathkey
// rule multiHop_inputSwapsExchangeFixedAmountOfInputCurrency {}



// doc: (vice-versa) :: User must Exactly receive the given output amount of output currency for the variable amounts of input currency, i.e : delta(currencyOut) == IV4Router.ExactOutputSingleParams.amountOut

rule singleHop_outputSwapsGiveFixedAmountsOfOutputCurrency {
    env e;
    IV4Router.ExactOutputSingleParams  params;
    require params.amountOut != 0; // skip opendelta calculations
    require params.zeroForOne;

    require params.poolKey.hooks != currentContract; 
    require getCurrencyDeltaExt(params.poolKey.currency1, currentContract) == 0; //deltaBefore(currencyOut)

    swapExactOutSingle(e,params);

    int256 delta1 = getCurrencyDeltaExt(params.poolKey.currency1, currentContract);

    assert delta1 == params.amountOut, "User must receiver exact given amount of output currency";
}

//@audit now create a rule for multi-hop output swap
// rule multiHop_outputSwapsGiveFixedAmountsOfOutputCurrency {}




//zx := certoraRun certora/confs/V4Router.conf

//--------------------------------------------------------------
//--------------------------------------------------------------
//--------------------------------------------------------------


// doc: Fixed input swaps must prevent sandwich attacks, in other words user must not receiver lesser tokens than expected
rule singleHop_inputSwapsPreventsSandwichAttack {
   env e;
   IV4Router.ExactInputSingleParams  params;
   require params.zeroForOne; 
   require params.poolKey.hooks != currentContract; 
   require getCurrencyDeltaExt(params.poolKey.currency1, currentContract) == 0; // start from settled/Taken state

   swapExactInSingle@withrevert(e,params);
   bool reverted = lastReverted;

   //@audit fails becauses deltaOut and amountoutmin was 0 prevent that case
   // but i told it to have it lesser than pram why

   assert getCurrencyDeltaExt(params.poolKey.currency1, currentContract) < params.amountOutMinimum => reverted, "Swap must revert if user receives lesser tokens then expected";
}

//@audit now make a similar rule for multiHop_inputSwap
// rule multiHop_inputSwapsPreventsSandwichAttack {}

//--------------------------------------------------------------
//--------------------------------------------------------------

// doc: fixed output swaps can't swap more amounts of input currency than the maximum limit provided by user, i.e: if a user wants to only allow swapping of upto 5 ETH for usdc, the swap must revert if output amount requires > 5 ETHs

rule singleHop_outputSwapCantTakeMoreInputCurrencyThanMaxLimit {
    env e;
    IV4Router.ExactOutputSingleParams  params;
    require params.zeroForOne;
    require params.poolKey.hooks != currentContract; 
    require getCurrencyDeltaExt(params.poolKey.currency0, currentContract) == 0; //deltaBefore(currencyOut)

    swapExactOutSingle@withrevert(e,params);
    bool reverted = lastReverted;

    mathint delta0 = to_mathint(-(getCurrencyDeltaExt(params.poolKey.currency0, currentContract)));

    
    assert delta0 > params.amountInMaximum => reverted, "swap must revert if more input tokens are required for fixed amount than the max input limit";
}

// @audit now write similar rule for multi hop output swap
// rule multiHop_outputSwapCantTakeMoreInputCurrencyThanMaxLimit {}

//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------

// doc: user should be able to swap his whole credit by "fixed_input_type_swaps" for variable amounts of another pool currency- which means the delta of the swapped credit must cancelout and become zero
rule CreditSwapCancelsOutTheDeltaOfCreditedCurrency__singleHop {
   env e;
   IV4Router.ExactInputSingleParams  params;
   require params.amountIn == 0; // only opendelta swaps
   require params.poolKey.hooks != currentContract; 

   // swap the credit
   swapExactInSingle(e,params);
   

   // caching post state
   mathint deltaOfSwappedCredit;
   if(params.zeroForOne) {
       deltaOfSwappedCredit = getCurrencyDeltaExt(params.poolKey.currency0, currentContract);
   } else {
       deltaOfSwappedCredit = getCurrencyDeltaExt(params.poolKey.currency1, currentContract);
   }

   assert deltaOfSwappedCredit == 0, "All the credit must be utilized as the swap is of fixed input swap";
}

//@audit now make a similar rule for multi-hop
// rule credit.....__multiHop {}

//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------
//---------------------------------------------------------------------------------

// doc: (vice-versa) :: user should be able to swap his whole debt by "fixed_output_type_swaps" for variable amount of another pool currency- which means the delta of the swapped debt must cancelout and become zero; one thing to note here is the zeroForOne calculations for debt is inversed
rule DebtSwapCancelsOutTheDeltaOfDebtCurrency__singleHop {
    env e;
    IV4Router.ExactOutputSingleParams  params;
    require params.amountOut == 0; // open delta cases only
    require params.poolKey.hooks != currentContract; 
    
    swapExactOutSingle(e,params);

   // caching post state
   mathint deltaOfSwappedDebt;
   if(params.zeroForOne) {
       deltaOfSwappedDebt = getCurrencyDeltaExt(params.poolKey.currency1, currentContract);
   } else {
       deltaOfSwappedDebt = getCurrencyDeltaExt(params.poolKey.currency0, currentContract);
   }

   assert deltaOfSwappedDebt == 0, "All the debt must be utilized when swapped in output type swaps";

}

//@audit now create a similar rule for multi_hop debt swap
// rule DebtSwapCancelsOutTheDeltaOfDebtCurrency__multiHop {}

