// please note that there still needs some adjustments in this rule, 
// i found this 1.5 hour before competition end, here i am just bootstrapping everythin
// and first had to report on cantina.xyz
// full explanation will be disclosed in my private repo's issues section
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




// @audit-issue : user is able to get multiple or different currency than intentended
// in report i will be sharing example of USDC -- {ETH-DAI}, where user gets full ETH for usdc amounts and cause fundloss i.e delta of currencies has been confused in implementation.
rule onlyOutputCurrencyMustBeGivenToUser {
    env e;
    IV4Router.ExactOutputParams params;
    require params.path.length == 1; //optimize computation for the prover
    require getCurrencyDeltaExt(params.currencyOut, currentContract) == 0;

    Conversions.PoolKey key; bool zeroForOne;
    (key , zeroForOne) = getPoolAndSwapDirection(e, params.path[0], params.currencyOut);

    require zeroForOne; // that means c0 == params.currencyOut
    //might need to inverse
    // require !zeroForOne; // that means c0 == params.currencyOut
    // might need to further manupilate param.path[]._data_fields


    // Conversions.PoolKey key; bool zeroForOne;
    // (key , zeroForOne) = getPoolAndSwapDirection(e, params.path[0], params.currencyIn);

    // bytes32 poolId = PoolKeyToId(key);
    require params.amountOut > 0;
    require params.amountInMaximum > 0;
   
    swapExactOut(e, params);

    assert getCurrencyDeltaExt(params.currencyOut, currentContract) < 0, "input currency must be taken from the user";
}

// init run (@note i have to modify it a lil bit more to make it more valid):=== 
// https://prover.certora.com/output/951980/b66c411a1bf1430ea20766afdb8b2682?anonymousKey=fab644db47ca370c123267327a4ad66f6126c013