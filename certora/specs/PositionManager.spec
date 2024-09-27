import "./setup/SafeTransferLibCVL.spec";
import "./setup/Deltas.spec";
import "./setup/EIP712.spec";
import "./setup/PoolManager.spec";

using PositionManagerHarness as Harness;

methods {
    function getPoolAndPositionInfo(uint256 tokenId) external returns (PositionManagerHarness.PoolKey, PositionManagerHarness.PositionInfo) envfree;
    function Harness.poolManager() external returns (address) envfree;
    function Harness.msgSender() external returns (address) envfree;

    // summaries for unresolved calls
    unresolved external in _._ => DISPATCH [
        PositionManagerHarness._
    ] default NONDET; 
    function _.permit(address,IAllowanceTransfer.PermitSingle,bytes) external => NONDET;
    function _.permit(address,IAllowanceTransfer.PermitBatch,bytes) external => NONDET;
    function _.isValidSignature(bytes32, bytes memory) internal => NONDET;
    function _.isValidSignature(bytes32, bytes) external => NONDET;
    function _._call(address, bytes memory) internal => NONDET;
    function _._call(address, bytes) external => NONDET;
    function _.notifyUnsubscribe(uint256, PositionManagerHarness.PositionInfo, bytes) external => NONDET;
    function _.notifyUnsubscribe(uint256, PositionManagerHarness.PositionInfo memory, bytes memory) internal => NONDET;
    function _.notifyUnsubscribe(uint256) external => NONDET;
    // likely unsound, but assumes no callback
    function _.onERC721Received(
        address operator,
        address from,
        uint256 tokenId,
        bytes data
    ) external => NONDET; /* expects bytes4 */
}

use builtin rule sanity;
definition address0() returns address = 0x0000000000000000000000000000000000000000;

//  adding positive liquidity results in currency delta change for PositionManager
rule increaseLiquidityDecreasesBalances(env e) {
    uint256 tokenId; uint256 liquidity; uint128 amount0Max; uint128 amount1Max; bytes hookData;
    
    PositionManagerHarness.PoolKey poolKey; PositionManagerHarness.PositionInfo info;

    (poolKey, info) = getPoolAndPositionInfo(tokenId);
    require poolKey.hooks != currentContract;

    int256 delta0Before = getCurrencyDeltaExt(poolKey.currency0, currentContract);
    int256 delta1Before = getCurrencyDeltaExt(poolKey.currency1, currentContract);

    // deltas must be 0 at the start of any tx
    require delta0Before == 0;
    require delta1Before == 0;

    increaseLiquidity(e, tokenId, liquidity, amount0Max, amount1Max, hookData);

    int256 delta0After = getCurrencyDeltaExt(poolKey.currency0, currentContract);
    int256 delta1After = getCurrencyDeltaExt(poolKey.currency1, currentContract);

    assert liquidity != 0 => delta0After != 0 || delta1After != 0;
}


rule positionManagerSanctioned(address token, method f, env e, calldataarg args) filtered {
    f -> f.selector != sig:settlePair(Conversions.Currency,Conversions.Currency).selector
    && f.selector != sig:settle(Conversions.Currency,uint256,bool).selector
    && f.selector != sig:takePair(Conversions.Currency,Conversions.Currency,address).selector
    && f.selector != sig:take(Conversions.Currency,address,uint256).selector
    && f.selector != sig:close(Conversions.Currency).selector
    && f.selector != sig:sweep(Conversions.Currency,address).selector
    && f.contract == currentContract
} {
    require e.msg.sender == msgSender(e);
    require e.msg.sender != currentContract;

    uint256 balanceBefore = balanceOfCVL(token, currentContract);
    
    f(e,args);

    uint256 balanceAfter = balanceOfCVL(token, currentContract);

    assert balanceAfter == balanceBefore;
}


rule lockerDoesntChange(method f, env e, calldataarg args) {
    address locker = msgSender(e); // calls _getLocker

    f(e,args);

    address newLocker = msgSender(e);

    assert newLocker == locker;
}


// doc: Every minted liquidity position must have its position information attached to it
invariant tokenIdIsMintedWithAttachedPositionInfoAlwaysAndViceVersa(env e, uint tokenId)
    ownerOf(e, tokenId) != address0() <=> positionInfo(e, tokenId) != emptyPositionInfo(e)
    // safe to filter this method, as the prover's havoc value messesup dirty upper bit calculations, otherwise safe
     filtered {
        f -> f.selector != sig:unsubscribe(uint256).selector
    }

// doc: Unminted positions must not hold any liquidities
rule onlyMintedPositionsHoldPositiveLiquidities {
    env e;
    calldataarg args;
    method f;
    uint256 tokenId;Conversions.PoolKey poolKey;int24 tickLower;int24 tickUpper;

    f(e,args);

    assert getLiquidityOf(e, tokenId, poolKey, tickLower, tickUpper) > 0 => ownerOf(e,tokenId) != address0(), "burnt positions must never hold any liquidity";
}

// doc: LPs must get unique liquidity positions
rule liquidtyPositionsAreMintedInIncreasingOrder(method f) filtered {
    // filter view and transfer methods
    f -> !f.isView && f.selector != sig:safeTransferFrom(address,address,uint256,bytes).selector && f.selector != sig:transferFrom(address,address,uint256).selector && f.selector != sig:safeTransferFrom(address,address,uint256).selector

}

{
    //general
    env e;
    calldataarg args;
    uint tokenIdBefore = nextTokenId(e);
    require tokenIdBefore < max_uint256;


    // special case for mint
    if (f.selector == sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector) {
    
    //prestate
    Conversions.PoolKey poolKey;
    int24 tickLower;
    int24 tickUpper;
    uint256 liquidity;
    uint128 amount0Max;
    uint128 amount1Max;
    address owner;
    bytes hookData;
    uint mint_userBalanceBefore = balanceOf(e,mapRecipient(e, owner));
    require mint_userBalanceBefore > 0 && mint_userBalanceBefore < max_uint256;

        
    //function call
    mintPosition(e, poolKey, tickLower,tickUpper,liquidity,amount0Max,amount1Max,owner,hookData);

    //post state    
    uint mint_userBalanceAfter = balanceOf(e,mapRecipient(e, owner));
    uint tokenIdAfter = nextTokenId(e);

    //assert 
    assert mint_userBalanceAfter > mint_userBalanceBefore <=> tokenIdAfter > tokenIdBefore, "liquidity postions must be minted with the higher id than the previously minted one" ;

    } else {

    //pre-state
    uint userBalanceBefore = balanceOf(e,mapRecipient(e, e.msg.sender));
    // prevent unrealistic overflow and underflow during mint/burn ops
    require userBalanceBefore > 0 && userBalanceBefore < max_uint256;

    //functioncall
    f(e, args);

    //post-state
    uint userBalanceAfter = balanceOf(e,mapRecipient(e, e.msg.sender));
    uint tokenIdAfter = nextTokenId(e);

    //assert
    assert userBalanceAfter > userBalanceBefore <=> tokenIdAfter > tokenIdBefore, "liquidity postions must be minted with the higher id than the previously minted one" ;

    }
}

// doc: liqudity of a given position must increase only with mint and increase operations
rule liquidityIncreasesOnlyWithMintAndIncreaseOperations {
    env e;
    method f;
    calldataarg args;


    bytes32 _id;
    bytes32 positionId;

    uint128 liquidityBefore = positionLiquidityPerPool[_id][positionId];

    f(e,args);

   
    uint128 liquidityAfter = positionLiquidityPerPool[_id][positionId];

    assert liquidityAfter > liquidityBefore => (f.selector == sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector) || (f.selector == sig:increaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector), "only mintPosition and increaseLiquidity must increase the liquidity of a given position";
}

// doc: (vice-versa) :: liqudity of a given position must decrease only with burn and decrease operations
rule liquidityDecreasesOnlyWithBurnAndDecreaseOperations {
    env e;
    method f;
    calldataarg args;
    
    bytes32 _id;
    bytes32 positionId;

    uint128 liquidityBefore = positionLiquidityPerPool[_id][positionId];

    f(e,args);

   
    uint128 liquidityAfter = positionLiquidityPerPool[_id][positionId];

    assert liquidityAfter < liquidityBefore => (f.selector == sig:burnPosition(uint256,uint128,uint128,bytes).selector) || (f.selector == sig:decreaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector), "only burnPosition and decreaseLiquidity must decrease the liquidity of a given position";
    
}

// doc: debt amount of a given currency can not be taken from the pool
rule debtMustAlwaysBeSettledNotTaken(method f) 
filtered {
    f -> f.selector != sig:increaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector && f.selector != sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector && f.selector != sig:decreaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector && f.selector != sig:burnPosition(uint256,uint128,uint128,bytes).selector && f.selector != sig:take(Conversions.Currency,address,uint256).selector
}
{
    
    env e; calldataarg args;
    Conversions.Currency currency; 
    int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);
    require deltaBefore < 0;
    f(e,args);
    int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);

    assert deltaAfter >= deltaBefore, "debt must be always be settled";
}

// doc: (vice-versa) :: credit amount of a given currency must be taken from the pool
rule creditMustBeTakenNotSettled(method f) 
filtered {
    f -> f.selector != sig:increaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector && f.selector != sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector && f.selector != sig:decreaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector && f.selector != sig:burnPosition(uint256,uint128,uint128,bytes).selector && f.selector != sig:settle(Conversions.Currency,uint256,bool).selector
}
{
    
    env e; calldataarg args;
    Conversions.Currency currency; 
    int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);
    require deltaBefore > 0;
    require _syncedCurrency == 0;
    f(e,args);
    int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);

    assert deltaAfter <= deltaBefore, "credit must be taken not settled";
}
   
// doc: debt settler functions must not decrease delta of a given currency
rule settleBasedActionsEitherIncreaseDeltaOrKeepitSame {
    env e; calldataarg args; method f;
    Conversions.Currency currency; 
    int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);
    require deltaBefore < 0;

    f(e,args);

    int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);
    assert settleBased(f) => deltaAfter >= deltaBefore; 
}

// doc: credit taker functions must not increase delta of a given currency
rule TakeBasedActionsEitherDecreaseDeltaOrKeepitSame { 
    env e; calldataarg args; method f;
    Conversions.Currency currency; 
    int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);
    require deltaBefore > 0;
    require _syncedCurrency == 0; // only in transient storage, _syncedCurrency > 0

    f(e,args);

    int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);
    assert takeBased(f) => deltaAfter <= deltaBefore;
}

// doc: only debt settler functions can increase delta of a given currency
rule onlySettleBasedActionsIncreaseDelta {

    env e; calldataarg args; method f;

    if(f.selector == sig:increaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector) {

        uint256 tokenId; uint256 liquidity; uint128 amount0Max; uint128 amount1Max; bytes hookData;
    
        PositionManagerHarness.PoolKey poolKey; PositionManagerHarness.PositionInfo info;

        (poolKey, info) = getPoolAndPositionInfo(tokenId);
        require poolKey.hooks != currentContract;

        int256 delta0Before = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1Before = getCurrencyDeltaExt(poolKey.currency1, currentContract);

        // deltas must be 0 at the start of any tx
        require delta0Before == 0;
        require delta1Before == 0;

        increaseLiquidity(e, tokenId, liquidity, amount0Max, amount1Max, hookData);

        int256 delta0After = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1After = getCurrencyDeltaExt(poolKey.currency1, currentContract);
        
        // adding liquidity decreases delta of a currency that is when settle based action increase delta and cancel out and reach empty value-0

        assert liquidity > 0 => delta0After < 0 && delta1After < 0;

    } else if (f.selector == sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector) {

       PositionManagerHarness.PoolKey poolKey;int24 tickLower;int24 tickUpper;uint256 liquidity;uint128 amount0Max;uint128 amount1Max;address owner;bytes  hookData;

        //important require
        require poolKey.hooks != currentContract;

        //delta
        int256 delta0Before = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1Before = getCurrencyDeltaExt(poolKey.currency1, currentContract);

        // deltas must be 0 at the start of any tx
        require delta0Before == 0;
        require delta1Before == 0;

        mintPosition(e,poolKey,tickLower,tickUpper,liquidity,amount0Max,amount1Max,owner,hookData);

        int256 delta0After = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1After = getCurrencyDeltaExt(poolKey.currency1, currentContract);

        // adding liquidity decreases delta of a currency that is when settle based action increase delta and cancel out and reach empty value-0

        assert liquidity > 0 => delta0After < 0 && delta1After < 0;

    } else {

        Conversions.Currency currency;
        int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);

        f(e,args);

        int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);

        assert deltaAfter > deltaBefore => settleBased(f) || f.selector == sig:decreaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector || f.selector == sig:burnPosition(uint256,uint128,uint128,bytes).selector; 

    }
}

// doc: (vice-versa) :: only credit taker functions can decrease delta of a given currency
rule onlyTakeBasedActionsDecreaseDelta {

    env e; calldataarg args; method f;

    if(f.selector == sig:decreaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector) {

        uint256 tokenId; uint256 liquidityWithdrawal; uint128 amount0Min; uint128 amount1Min; bytes hookData;
    
        PositionManagerHarness.PoolKey poolKey; PositionManagerHarness.PositionInfo info;

        (poolKey, info) = getPoolAndPositionInfo(tokenId);
        require poolKey.hooks != currentContract;

        int256 delta0Before = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1Before = getCurrencyDeltaExt(poolKey.currency1, currentContract);

        // deltas must be 0 at the start of any tx
        require delta0Before == 0;
        require delta1Before == 0;

        // method call
        decreaseLiquidity(e,tokenId, liquidityWithdrawal, amount0Min, amount1Min,hookData);

        int256 delta0After = getCurrencyDeltaExt(poolKey.currency0, currentContract);
        int256 delta1After = getCurrencyDeltaExt(poolKey.currency1, currentContract);
        
        // removing liquidity increases delta of a currency that is when take based action decrease delta and cancel out and reach empty value- 0

        assert liquidityWithdrawal > 0 => delta0After > 0 && delta1After > 0;

    } else if (f.selector == sig:burnPosition(uint256,uint128,uint128,bytes).selector) {

    uint256 tokenId; int24 tickLower;int24 tickUpper;uint128 amount0Min;uint128 amount1Min; bytes  hookData; uint128 liquidityWithdrawal;

    PositionManagerHarness.PoolKey poolKey; PositionManagerHarness.PositionInfo info;

    (poolKey, info) = getPoolAndPositionInfo(tokenId);
    require poolKey.hooks != currentContract;

    //delta
    int256 delta0Before = getCurrencyDeltaExt(poolKey.currency0, currentContract);
    int256 delta1Before = getCurrencyDeltaExt(poolKey.currency1, currentContract);

    // deltas must be 0 at the start of any tx
    require delta0Before == 0;
    require delta1Before == 0;

    // liquidity must be greater than 0 
    liquidityWithdrawal = getLiquidityOf(e,tokenId,poolKey, tickLower, tickUpper);

    burnPosition(e,tokenId,amount0Min,amount1Min,hookData);

    int256 delta0After = getCurrencyDeltaExt(poolKey.currency0, currentContract);
    int256 delta1After = getCurrencyDeltaExt(poolKey.currency1, currentContract);

    // removing liquidity increases delta of a currency that is when take based action decrease delta and cancel out and reach empty value- 0

    assert liquidityWithdrawal > 0 => delta0After > 0 && delta1After > 0;

} else {

        Conversions.Currency currency; 
        int256 deltaBefore = getCurrencyDeltaExt(currency,currentContract);
        
        f(e,args);

        int256 deltaAfter = getCurrencyDeltaExt(currency,currentContract);

        assert deltaAfter < deltaBefore => takeBased(f) || f.selector == sig:mintPosition(Conversions.PoolKey,int24,int24,uint256,uint128,uint128,address,bytes).selector || f.selector == sig:increaseLiquidity(uint256,uint256,uint128,uint128,bytes).selector; 

    }


}

// doc: Liqudity of a given position must always be modified with proper authorization
rule liqudityOfPositionCanOnlyBeModifiedByApprovedUser {
    env e;
    calldataarg args;
    method f;
    uint256 tokenId;Conversions.PoolKey poolKey;int24 tickLower;int24 tickUpper;
    uint128 liquidityBefore = getLiquidityOf(e, tokenId, poolKey, tickLower, tickUpper);
    
    address owner;

    f(e,args);
    
    uint128 liquidityAfter = getLiquidityOf(e, tokenId, poolKey, tickLower, tickUpper);
    
    assert liquidityAfter > liquidityBefore || liquidityAfter < liquidityBefore => authorized(e, owner, e.msg.sender, tokenId);

}

// doc: liqudity position can only subscribed or unsubscribed by expected methods
rule noUnexpectedSubscribeOrUnsubscribeOperationOccurs {
    env e; calldataarg args; method f;
    uint tokenId;
    address subscriberBefore =  subscriber(e, tokenId);
    f(e,args);
    address subscriberAfter =  subscriber(e, tokenId);

    assert (subscriberBefore == address0() && subscriberAfter > address0() => f.selector == sig:subscribe(uint256,address,bytes).selector) && ((subscriberBefore != address0() && subscriberAfter == address0()) => f.selector == sig:burnPosition(uint256,uint128,uint128,bytes).selector || f.selector == sig:unsubscribe(uint256).selector);

}

// doc: liquidity position must only be subscribed or unsubscribed with proper authorization
rule positionSubscriptionsCanOnlyBeModifiedByAuthorizedParties {
    env e; calldataarg args; method f;
    uint tokenId; address owner;

    address subscriberBefore =  subscriber(e, tokenId);
    f(e,args);
    address subscriberAfter =  subscriber(e, tokenId);

    // since both subscribe and unsubscribe operations change before subscriptions state,  0-n || n-0 
    assert subscriberBefore != subscriberAfter => authorized(e,owner,e.msg.sender,tokenId);
}

// doc: subscriber of a liqudity position can't be overriden without unsubscribing him first
rule subscriberCantBeAddedWithoutUnsubscribingFormer {
    env e; calldataarg args; method f;
    uint tokenId;
    address subscriberBefore =  subscriber(e, tokenId);
    f(e,args);
    address subscriberAfter =  subscriber(e, tokenId);

    assert subscriberBefore > address0() => subscriberAfter == subscriberBefore || subscriberAfter == address0();
}

// doc: liqudity positions must be transferred correctly
rule approvedTransfersUpdatesOwnership {
    env e;
    address from; address to; uint256 id;

    transferFrom(e, from, to, id);

    assert ownerOf(e, id) == to, "after transfer operation, receiver must become the owner of the nft id";

}

// doc: liquidity positions must be minted as per the recepient mapping
rule positionsAreMinted_asPer_recepientMapping {
        env e;
        Conversions.PoolKey poolKey;
        int24 tickLower;
        int24 tickUpper;
        uint256 liquidity;
        uint128 amount0Max;
        uint128 amount1Max;
        address owner;
        bytes hookData;

        address intendedReceiver = mapRecipient(e, owner);
        uint receiverBalanceBefore = balanceOf(e, intendedReceiver);
        //prevent unrealistic overflow
        require receiverBalanceBefore < max_uint256; 

        mintPosition(e, poolKey, tickLower,tickUpper,liquidity,amount0Max,amount1Max,owner,hookData);

        assert balanceOf(e, intendedReceiver) > receiverBalanceBefore, "positions must be minted according to the recepient mapping";
}

//============================================================//
//                   H E L P E R S
//============================================================//

function settleBased(method f) returns bool {
    return (f.selector == sig:settlePair(Conversions.Currency,Conversions.Currency).selector || f.selector == sig:settle(Conversions.Currency,uint256,bool).selector || f.selector == sig:close(Conversions.Currency).selector);
}

function takeBased(method f )returns bool {
    // return true; //impl
    return (f.selector == sig:takePair(Conversions.Currency, Conversions.Currency,address).selector || f.selector == sig:take(Conversions.Currency, address, uint256).selector || f.selector == sig:clearOrTake(Conversions.Currency, uint256).selector || f.selector == sig:close(Conversions.Currency).selector);
}


function authorized(env e, address owner, address spender, uint tokenId) returns bool {
    require owner == ownerOf(e, tokenId);
    return (spender == owner  || isApprovedForAll(e,owner, spender) || spender == getApproved(e, tokenId));
}