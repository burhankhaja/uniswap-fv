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

// zx :=    certoraRun certora/confs/V4RouterSqrtPrice.conf --rule ""

definition MIN_SQRT_PRICE() returns uint160 = 4295128739;
definition MAX_SQRT_PRICE() returns uint160 = 1461446703485210103287273052203988822378723970342;
        
// doc: single-hop swaps can increase or decrease price limit by any value in between min and max sqrtprice bounds
rule ValueBetweenMinMaxBoundsPushesSqrtPriceInSingleInputSwap {
    env e;
    IV4Router.ExactInputSingleParams params;
    bytes32 poolId = PoolKeyToId(params.poolKey);

    swapExactInSingle(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert params.sqrtPriceLimitX96 != 0 => sqrtP == params.sqrtPriceLimitX96;
    assert params.sqrtPriceLimitX96 == 0 && params.zeroForOne => sqrtP == (MIN_SQRT_PRICE() + 1);
    assert params.sqrtPriceLimitX96 == 0 && !params.zeroForOne => sqrtP == (MAX_SQRT_PRICE() - 1);
}

rule ValueBetweenMinMaxBoundsPushesSqrtPriceInSingleOutputSwap {
    env e;
    IV4Router.ExactOutputSingleParams params;
    bytes32 poolId = PoolKeyToId(params.poolKey);

    swapExactOutSingle(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert params.sqrtPriceLimitX96 != 0 => sqrtP == params.sqrtPriceLimitX96;
    assert params.sqrtPriceLimitX96 == 0 && params.zeroForOne => sqrtP == (MIN_SQRT_PRICE() + 1);
    assert params.sqrtPriceLimitX96 == 0 && !params.zeroForOne => sqrtP == (MAX_SQRT_PRICE() - 1);
}


// doc: multi-hop swaps must increase or decrease price only by a value closely next to min and max sqrtprice bound
rule sqrtPriceLimitIsPushedByValueCloserToMinMaxLimits_inputSwap {
    env e;
    
    IV4Router.ExactInputParams params;
    require params.path.length == 1; //optimize computation for the prover

    //need to calculate poolkey, poolId
    Conversions.PoolKey key; bool zeroForOne;
    (key , zeroForOne) = getPoolAndSwapDirection(e, params.path[0], params.currencyIn);

    bytes32 poolId = PoolKeyToId(key);

    swapExactIn(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert zeroForOne => sqrtP == (MIN_SQRT_PRICE() + 1);
    assert !zeroForOne => sqrtP == (MAX_SQRT_PRICE() - 1);

}



//@audit checkpoint @audit-issue it is lil bit inverse :::: currencyOUt is passed
rule sqrtPriceLimitIsPushedByValueCloserToMinMaxLimits_outputSwap {
    env e;
    
    
    IV4Router.ExactOutputParams
    require params.path.length == 1; //optimize computation for the prover

    bytes32 poolId = PoolKeyToId(params.poolKey);

    swapExactOut(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert params.zeroForOne => sqrtP == ;
    assert !params.zeroForOne => sqrtP == ;
}

//==================================================
//==================================================
//==================================================
//          G E N E R A L      R U L E S
//==================================================
//==================================================

rule SUMMARIZED_ValueBetweenMinMaxBoundsPushesSqrtPriceInSingleInputSwap {
    env e;
    IV4Router.ExactInputSingleParams params;
    bytes32 poolId = PoolKeyToId(params.poolKey);

    swapExactInSingle(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert (sqrtP == params.sqrtPriceLimitX96 || sqrtP == (MIN_SQRT_PRICE() + 1) || sqrtP == (MAX_SQRT_PRICE() - 1));
}

rule SUMMARIZED_ValueBetweenMinMaxBoundsPushesSqrtPriceInSingleOutputSwap {
    env e;
    IV4Router.ExactOutputSingleParams params;
    bytes32 poolId = PoolKeyToId(params.poolKey);

    swapExactOutSingle(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert (sqrtP == params.sqrtPriceLimitX96 || sqrtP == (MIN_SQRT_PRICE() + 1) || sqrtP == (MAX_SQRT_PRICE() - 1));
}

rule SUMMARIZED_sqrtPriceLimitIsPushedByValueCloserToMinMaxLimits_inputSwap {
    env e;
    
    IV4Router.ExactInputParams params;
    require params.path.length == 1; //optimize computation for the prover

    //need to calculate poolkey, poolId
    Conversions.PoolKey key; bool zeroForOne;
    (key , zeroForOne) = getPoolAndSwapDirection(e, params.path[0], params.currencyIn);

    bytes32 poolId = PoolKeyToId(key);

    swapExactIn(e, params);

    uint160 sqrtP = poolSqrtPriceX96[poolId];

    assert (sqrtP == (MIN_SQRT_PRICE() + 1)) || (sqrtP == (MAX_SQRT_PRICE() - 1));

}


