// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;
/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Returns the balance of tokens.
     */
    function decimals() external view returns (uint8);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) return (true, 0);
        uint256 c = a * b;
        if (c / a != b) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a % b);
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: division by zero");
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b > 0, "SafeMath: modulo by zero");
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        return a - b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryDiv}.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        return a % b;
    }
}



/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{ value: amount }("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
      return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{ value: value }(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data, string memory errorMessage) internal view returns (bytes memory) {
        require(isContract(target), "Address: static call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.staticcall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(bool success, bytes memory returndata, string memory errorMessage) private pure returns(bytes memory) {
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}





/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value, "SafeERC20: decreased allowance below zero");
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address.functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }
}

interface IStaking {
    function transferToZino( address token, uint256 tokenAmount) external;
    function tradeProfitsToCollateral(
        address _user,
        address _token,
        uint256 _amount
    ) external;
    function tradeLossToCollaterals(
        address _user, 
        address lossToken, 
        uint256 lossAmt
    ) external;
    function updateTradeUsingAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external;
    function updateLockAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external;
    function spotTradeCollaterals(address _user, address _tokenIn, uint256 _amountIn,address _tokenOut, uint256 _amountOut) external;
    function getUserInfo(address _user) external view returns (UserInfo[] memory);
    function isListToken(address _token) external view returns(bool status);
    function getPidByToken(address _token) external view returns(uint256 _pid);
    function getTotalValueUsable(address _token) external view returns(uint256 _amount);
    function referralInfo(address _user)external view returns(ReferralInfo memory);
    function updateInterPool(address _tokenIn, uint256 _amountIn, address _tokenOut, uint256 _amountOut) external;
    function updateReferralInfo(address _referrer, uint256 sumAmt, uint256 feeAmt) external;
    function depositToVault(address _token) external;
    function increasePoolSrcDstAmt(address _token, uint256 _amount, bool _type) external;
    function liquidate(address _user, bool _type) external;
}
interface ISwapProxy {
    function swap(
        bytes memory swapCallData,
        uint ethAmt,
        uint256 amountIn,
        address tokenIn
    ) external payable returns (uint) ;
}
interface IParaSwapAugustus {
  function getTokenTransferProxy() external view returns (address);
}
interface IPriceOracle {
    function getPrice(address _token) external view returns( uint256 );
}

struct ReferralInfo {
    address referrer;
    uint256 amountUSD;
    uint256 feeUSD;
    uint256 count;
}
struct UserInfo {
    address token;
    uint256 lockAmt;
    uint256 lockUSD;
    uint256 reqWithdrawAmt;
    uint256 reqWithdrawUSD;
    uint256 tradeCollateralAmt;
    uint256 tradeCollateralUSD;
    uint256 borrowCollateralAmt;
    uint256 borrowCollateralUSD;
    uint256 unlockTime;
    uint256 claimableAmt;
    uint256 claimableUSD;
    uint256 lastClaimTime;
}
interface IWETH {
    function deposit() external payable;
    function withdraw(uint wad) external;
    function transfer(address to, uint value) external returns (bool);
    function balanceOf(address account) external view returns (uint);
}
interface IDataStore {
    function updateData(
        uint256 _type,
        address _user,
        uint256 _userAmount,
        uint256 _poolAmount
    ) external;
}
contract Trade is ReentrancyGuard{
    using SafeERC20 for IERC20;
    struct MarketPair{
        address longtoken; // index Token like WETH
        address shorttoken; // stable Token like USDC
    }
    struct TradeInfo{
        uint256 id;
        address trader;
        address tokenIn;
        uint256 amountIn;
        address tokenOut;
        uint256 amountOut;
        uint256 updateTime;
        uint256 feeAmount;
        uint256 openPrice;
        uint256 closePrice;
        int256 profitUSD;
    }
    struct TradeCloseInfo{
        uint256 id;
        address trader;
        bool tradetype;
        address indexToken;
        uint256 indexAmount;
        uint256 indexUSD;
        uint256 closeTime;
        uint256 openPrice;
        uint256 closePrice;
        int256 profitUSD;
    }
    struct TradeDetailInfo{
        uint256 id;
        address trader;
        bool tradetype; // long: true, short: false
        address indexToken;
        uint256 indexAmount;
        address stableToken;
        uint256 stableAmount;
        uint256 indexUSD;
        uint256 entryPrice;
        uint256 marketPrice;
        uint256 liqPrice;
        uint256 feeAmount;
        uint256 feeUSD;
    }
    struct PreviewInParam{
        address user;
        address token;
        uint256 amount;
        address indexToken;
    }
    struct LimitOrderInfo{
        address user;
        uint256 orderTime;
        uint256 limitorderId;
        address tokenIn;
        uint256 amountIn;
        address tokenOut;
        address indexToken;
        uint256 indexAmount;
        uint256 indexUSD;
        uint256 limitPrice;
        uint256 upPrice;
        uint256 downPrice;
        bool highStart;
        bool openPerform;
        uint256 openId;
        bool status;
    }
    event Response(bool success, bytes data, uint256 buyAmt);

    address public constant weth = 0x82aF49447D8a07e3bd95BD0d56f35241523fBab1;
    address public datastore;
    
    address constant public priceoracle = 0x2bE2f60Df305E4Ec5cDB88EEDD686c4CE473Fd52;
    mapping( address => uint256 ) public usingfeeapr;
    mapping( address => address ) public altexecutor;
    mapping ( uint256 => TradeInfo ) public tradeinfo;
    MarketPair[] public marketpair;
    mapping ( uint256 => LimitOrderInfo ) public limitorderinfo;
    mapping( address => uint256[] ) public userOpenIds;
    mapping( address => uint256[] ) public userCloseIds;
    mapping( address => uint256[] ) public userlimitOrderIds;
    address[] public OpenedUsers;
    uint256 public openId = 1;
    uint256 public limitorderId = 1;
    address public operator;
    address public  staking;
    address[] public swapProxyArray;
    uint256 constant public tradeLimit_Down = 0; // 50 $50
    mapping( address => uint256) public tradeLimit_Up;
    uint256 public MAXMULTIPLY = 100;
    address public executor;
    uint256 constant public tradeapr = 300; // 300 : 3%,  10000 : 100%
    uint256 public percentRate = 10000;
    uint256 public feePeriod = 365 days;
    uint256 public tradeFeeRate = 6; // 6: 0.06%
    uint256 public referralFeeRate = 1000; // 10%
    address public treasury;


    constructor(address _staking){
        operator = msg.sender;
        executor = msg.sender;
        treasury = msg.sender;
        setStaking(_staking);
        addProxy(0x111111125421cA6dc452d289314280a0f8842A65); // 1inchswap router v6
        addProxy(0x6A000F20005980200259B80c5102003040001068); // paraswap router v6.2
        addProxy(0xDef1C0ded9bec7F1a1670819833240f027b25EfF); // 0x exchange router

        usingfeeapr[0x82aF49447D8a07e3bd95BD0d56f35241523fBab1] = 6000; // WETH
        usingfeeapr[0xFd086bC7CD5C481DCC9C85ebE478A1C0b69FCbb9] = 7000; // USDT
        usingfeeapr[0xaf88d065e77c8cC2239327C5EDb3A432268e5831] = 7000; // USDC
        usingfeeapr[0x2f2a2543B76A4166549F7aaB2e75Bef0aefC5B0f] = 6000; // WBTC
        usingfeeapr[0xFF970A61A04b1cA14834A43f5dE4533eBDDB5CC8] = 7000; // USDC.e
        usingfeeapr[0xFa7F8980b0f1E64A2062791cc3b0871572f1F7f0] = 6000; // UNI
        usingfeeapr[0x0c880f6761F1af8d9Aa9C466984b80DAb9a8c9e8] = 6000; // Pendle
        usingfeeapr[0x912CE59144191C1204E64559FE8253a0e49E6548] = 6000; // ARB
        usingfeeapr[0xf97f4df75117a78c1A5a0DBb814Af92458539FB4] = 6000; // LINK
        usingfeeapr[0x5979D7b546E38E414F7E9822514be443A4800529] = 6000; // wstETH
        usingfeeapr[0xEC70Dcb4A1EFa46b8F2D97C310C9c4790ba5ffA8] = 6000; // rETH
        usingfeeapr[0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe] = 6000; // weETH
        usingfeeapr[0x2416092f143378750bb29b79eD961ab195CcEea5] = 6000; // ezETH
        usingfeeapr[0xfc5A1A6EB076a2C7aD06eD22C90d7E710E35ad0a] = 6000; // GMX


        tradeLimit_Up[0x82aF49447D8a07e3bd95BD0d56f35241523fBab1] = 50000000000000; // WETH 500kUSD
        tradeLimit_Up[0x2f2a2543B76A4166549F7aaB2e75Bef0aefC5B0f] = 50000000000000; // WBTC 500kUSD
        tradeLimit_Up[0xFa7F8980b0f1E64A2062791cc3b0871572f1F7f0] = 5000000000000; // UNI 50kUSD
        tradeLimit_Up[0x0c880f6761F1af8d9Aa9C466984b80DAb9a8c9e8] = 3000000000000; // Pendle 30kUSD
        tradeLimit_Up[0x912CE59144191C1204E64559FE8253a0e49E6548] = 30000000000000; // ARB  300kUSD
        tradeLimit_Up[0xf97f4df75117a78c1A5a0DBb814Af92458539FB4] = 5000000000000; // LINK 50kUSD
        tradeLimit_Up[0x5979D7b546E38E414F7E9822514be443A4800529] = 50000000000000; // wstETH 500kUSD
        tradeLimit_Up[0xEC70Dcb4A1EFa46b8F2D97C310C9c4790ba5ffA8] = 50000000000000; // rETH 500kUSD
        tradeLimit_Up[0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe] = 50000000000000; // weETH 500kUSD
        tradeLimit_Up[0x2416092f143378750bb29b79eD961ab195CcEea5] = 50000000000000; // ezETH 500kUSD
        tradeLimit_Up[0xfc5A1A6EB076a2C7aD06eD22C90d7E710E35ad0a] = 3000000000000; // GMX 30kUSD

        address[] memory indexTokens = new address[](11);
        indexTokens[0] = 0x82aF49447D8a07e3bd95BD0d56f35241523fBab1; // WETH 500kUSD
        indexTokens[1] = 0x2f2a2543B76A4166549F7aaB2e75Bef0aefC5B0f; // WBTC 500kUSD
        indexTokens[2] = 0xFa7F8980b0f1E64A2062791cc3b0871572f1F7f0; // UNI 50kUSD
        indexTokens[3] = 0x0c880f6761F1af8d9Aa9C466984b80DAb9a8c9e8; // Pendle 30kUSD
        indexTokens[4] = 0x912CE59144191C1204E64559FE8253a0e49E6548; // ARB  300kUSD
        indexTokens[5] = 0xf97f4df75117a78c1A5a0DBb814Af92458539FB4; // LINK 50kUSD
        indexTokens[6] = 0x5979D7b546E38E414F7E9822514be443A4800529; // wstETH 500kUSD
        indexTokens[7] = 0xEC70Dcb4A1EFa46b8F2D97C310C9c4790ba5ffA8; // rETH 500kUSD
        indexTokens[8] = 0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe; // weETH 500kUSD
        indexTokens[9] = 0x2416092f143378750bb29b79eD961ab195CcEea5; // ezETH 500kUSD
        indexTokens[10] = 0xfc5A1A6EB076a2C7aD06eD22C90d7E710E35ad0a; // GMX 30kUSD

        address[] memory stableTokens = new address[](3);
        stableTokens[0] = 0xFd086bC7CD5C481DCC9C85ebE478A1C0b69FCbb9; // USDT
        stableTokens[1] = 0xaf88d065e77c8cC2239327C5EDb3A432268e5831; // USDC
        stableTokens[2] = 0xFF970A61A04b1cA14834A43f5dE4533eBDDB5CC8; // USDC.e
        addMarketPairsIndexStable(indexTokens,stableTokens);
        
    }
    modifier onlyOperator() {
        require(operator == msg.sender, "trading: caller is not the operator");
        _;
    }
    modifier onlyExecutor() {
        require(executor == msg.sender, "trading: caller is not the executor");
        _;
    }
    function addMarketPairsIndexStable(address[] memory _indexTokens, address[] memory _stableTokens) public onlyOperator(){
        for(uint256 i = 0 ; i < _indexTokens.length ; i++){
            for(uint256 j = 0 ; j < _stableTokens.length ; j++){
                marketpair.push( MarketPair({
                    longtoken: _indexTokens[i],
                    shorttoken: _stableTokens[j]
                }));
            }
        }
    }
    // set functions by operator
    function addMarketPair(address[] memory _long, address[] memory _short) public onlyOperator{
        require(_long.length == _short.length, "different length");
        for( uint256 i = 0 ; i < _long.length ; i++){
            marketpair.push( MarketPair({
                longtoken: _long[i],
                shorttoken: _short[i]
            }));
        }
    }
    function delMarketPair(uint256 _index) public onlyOperator{
        for (uint i = _index; i < marketpair.length - 1; i++) {
            marketpair[i] = marketpair[i + 1];
        }
        marketpair.pop();
    }
    function getAllMarketPairs() public view returns(MarketPair[] memory){
        return marketpair;
    }

    function addProxy(address _proxy) public onlyOperator{
        swapProxyArray.push(_proxy);
    }
    function delProxy(address _proxy) public onlyOperator{
        uint _index;
        for ( _index = 0; _index < swapProxyArray.length ; _index ++){
            if(swapProxyArray[_index]==_proxy){
                break;
            }
        }
        if(_index < swapProxyArray.length){
            for (uint i = _index; i < swapProxyArray.length - 1; i++) {
                swapProxyArray[i] = swapProxyArray[i + 1];
            }
            swapProxyArray.pop();
        }
    }
    function setUsingFeeApr( address[] memory _usingtokens, uint256[] memory _aprs ) public onlyExecutor{
        require(_usingtokens.length == _aprs.length, "Invalid input length");
        for (uint256 i = 0; i < _usingtokens.length; i++) {
            usingfeeapr[_usingtokens[i]] = _aprs[i];
        }
    }

    function setStaking( address _staking) public onlyOperator {
        staking = _staking;
    }
    function setExecutor( address _executor) public onlyOperator {
        executor = _executor;
    }
    function setOperator( address _operator) public onlyOperator {
        operator = _operator;
    }
    function setDataStore( address _datastore) public onlyOperator {
        datastore = _datastore;
    }
    function setMAXMULTIPLY(uint256 _value) public onlyOperator{
        MAXMULTIPLY = _value;
    }

    // user functions

    function updateAltExecutor(bool _set) public {
        if(_set){
            altexecutor[msg.sender] = executor;
        }
        else{
            altexecutor[msg.sender] = msg.sender;
        }
    }

    function spotTradeWithCollateral(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address tokenIn,
        uint256 amountIn,
        address tokenOut
    ) public nonReentrant returns (uint buyAmt)  {
        require(IStaking(staking).getTotalValueUsable(tokenIn) >= amountIn, "Total Usable Balance overflow");
        buyAmt = trade(msg.sender, swapDataParam, swapProxy_index, tokenIn, amountIn, tokenOut);
        IStaking(staking).spotTradeCollaterals(msg.sender, tokenIn, amountIn, tokenOut, buyAmt);
    }
    function trade(
        address _user,
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address tokenIn,
        uint256 amountIn,
        address tokenOut
    ) internal returns (uint buyAmt)  {
        IStaking(staking).transferToZino( tokenIn, amountIn);
        // calculate the balance of swap tokens
        uint256 tokenInBal_pre = IERC20(tokenIn).balanceOf(address(this));
        uint256 tokenOutBal_pre = IERC20(tokenOut).balanceOf(address(this));
        // swap using the swapProxy
        IERC20(tokenIn).approve(swapProxyArray[swapProxy_index], amountIn);
        (bool success, bytes memory returnData) = swapProxyArray[swapProxy_index].call{value: 0}(swapDataParam);
        require(success, "swap-failed");
        uint _buyAmt = abi.decode(returnData, (uint256));
        // calculate the balance of swap tokens
        uint256 tokenInBal = IERC20(tokenIn).balanceOf(address(this));
        uint256 tokenOutBal = IERC20(tokenOut).balanceOf(address(this));
        require(tokenInBal_pre > tokenInBal && tokenOutBal > tokenOutBal_pre, "balance difference error");
        require(tokenInBal_pre - tokenInBal == amountIn && tokenOutBal - tokenOutBal_pre == _buyAmt, "balance amount error after swap");
        buyAmt = _buyAmt * (percentRate-tradeFeeRate) / percentRate;
        IERC20(tokenOut).transfer(staking, buyAmt);
        uint256 feeAmt = _buyAmt - buyAmt;
        if(IStaking(staking).referralInfo(_user).referrer != address(0)){
            IERC20(tokenOut).transfer(IStaking(staking).referralInfo(_user).referrer, feeAmt * referralFeeRate / percentRate); // fee amount
            IStaking(staking).updateReferralInfo(
                IStaking(staking).referralInfo(_user).referrer, 
                getAssetInUSD(tokenOut, _buyAmt),
                getAssetInUSD(tokenOut, feeAmt * referralFeeRate / percentRate)
            );
            feeAmt -= (feeAmt * referralFeeRate / percentRate);
        }
        IERC20(tokenOut).transfer(treasury, feeAmt);
        IStaking(staking).depositToVault(tokenOut);
        uint256 _volumeUSD = getAssetInUSD(tokenOut, _buyAmt);
        IDataStore(datastore).updateData(
            7,
            _user,
            _volumeUSD,
            _volumeUSD
        );
    }
    function checkOpenIdInUserInfo(address _user, uint256 _openId) internal view returns(bool){
        bool _exist = false;
        for(uint256 i = 0; i < userOpenIds[_user].length; i++){
            if(_openId == userOpenIds[_user][i]){
                _exist = true;
            }
        }
        return _exist;
    }
    function limitOrder(
        address _tokenIn,
        uint256 _amountIn,
        address _tokenOut,
        address _indexToken,
        uint256 _limitPrice,
        uint256 _upPrice,
        uint256 _downPrice,
        bool _openPerform, // true: open order, false: close order
        uint256 _openId
    ) public nonReentrant{
        bool _highStart;
        // check if the limit order amount is available
        if(_openPerform){ // open limit order
            (bool pairCk, address longtoken) = checkMarketPair(_tokenIn, _tokenOut);
            require(pairCk, "can't find the token pair");
            require(longtoken == _indexToken, "Invalid Index Token");
            require(IStaking(staking).getTotalValueUsable(_tokenIn) >= _amountIn, "Total Usable Balance overflow");
            require(getTradableTokenAmt(msg.sender, _tokenIn) >= _amountIn, "User Tradable Balance overflow");
            if(_tokenOut == _indexToken){
                _highStart = false;
            }
            else{
                _highStart = true;
            }
        }
        else{ // close limit order
            // check if this user has this openId
            require(checkOpenIdInUserInfo(msg.sender, _openId), "You don't have this openId");
            if(_tokenOut == _indexToken){
                _highStart = true;
            }
            else{
                _highStart = false;
            }
        }
        
        limitorderinfo[limitorderId] = LimitOrderInfo({
            user: msg.sender,
            orderTime: block.timestamp,
            limitorderId: limitorderId,
            tokenIn: _tokenIn,
            amountIn: _amountIn,
            tokenOut: _tokenOut,
            indexToken: _indexToken,
            indexAmount: getUSDInAsset(_tokenOut, getAssetInUSD(_tokenIn, _amountIn)),
            indexUSD: getAssetInUSD(_tokenIn, _amountIn),
            limitPrice: _limitPrice,
            upPrice: _upPrice,
            downPrice: _downPrice,
            highStart: _highStart,
            openPerform: _openPerform,
            openId: _openId,
            status: true
        });
        userlimitOrderIds[msg.sender].push(limitorderId);
        limitorderId++;
    }
    function cancelLimitOrder(uint256 _limitorderId, uint8 _type) public{
        address _user = limitorderinfo[_limitorderId].user;
        require(msg.sender ==  _user, "Caller is not the owner of the limitorder");
        require(limitorderinfo[_limitorderId].status, "Already canceled");
        if(_type == 1){ // upPrice cancel
            limitorderinfo[_limitorderId].upPrice = 0;
        }
        else if(_type == 2){ // downPrice cancel
            limitorderinfo[_limitorderId].downPrice = 0;
        }
        if(_type == 0 || 
           (limitorderinfo[_limitorderId].upPrice == 0 && 
            limitorderinfo[_limitorderId].downPrice == 0 && 
            limitorderinfo[_limitorderId].openPerform == false)
        ){
            limitorderinfo[_limitorderId].status = false;
            removeLimitOrderId(_user, _limitorderId);
        }
    }
    function cancelAllLimitOrder(address _user) public{
        require(_user ==  msg.sender, "You don't have permission");
        while(userlimitOrderIds[_user].length > 0){
            uint256 _limitorderId = userlimitOrderIds[_user][userlimitOrderIds[_user].length-1];
            limitorderinfo[_limitorderId].status = false;
            removeLimitOrderId(_user, _limitorderId);
        }
    }
    function limitOrderExecute(
        bytes[] memory swapDataParam,
        uint256[] memory swapProxy_index,
        uint256[] memory _ids
    ) public onlyExecutor {
        require(swapDataParam.length == swapProxy_index.length && swapDataParam.length == _ids.length, "lengths are not matched");
        for(uint256 i = 0 ; i < swapDataParam.length ; i++){
            require(limitorderinfo[_ids[i]].status, "This is canceled limitorder");
            if(limitorderinfo[_ids[i]].openPerform){ // open order limit case
                openPosition(limitorderinfo[_ids[i]].user, swapDataParam[i], swapProxy_index[i], limitorderinfo[_ids[i]].tokenIn, limitorderinfo[_ids[i]].amountIn, limitorderinfo[_ids[i]].tokenOut);
                if(limitorderinfo[_ids[i]].upPrice > 0 || limitorderinfo[_ids[i]].downPrice > 0){
                    limitorderinfo[_ids[i]].openPerform = false;
                    limitorderinfo[_ids[i]].openId = openId - 1;
                }
                else{
                    limitorderinfo[_ids[i]].status = false;
                    removeLimitOrderId(limitorderinfo[_ids[i]].user, _ids[i]);
                }
            }
            else{
                closePosition(swapDataParam[i], swapProxy_index[i], limitorderinfo[_ids[i]].openId);
                limitorderinfo[_ids[i]].status = false;
            }
        }
    }
    
    function removeLimitOrderId(address _user, uint256 _limitorderid) internal returns(bool){
        uint256 len = userlimitOrderIds[_user].length;
        uint256 _index;
        bool idexisted = false;
        for( _index = 0 ; _index < len ; _index++){
            if(userlimitOrderIds[_user][_index] == _limitorderid){   
                idexisted = true; 
                break;
            }
        }
        if(idexisted){
            for( ; _index < len - 1 ; _index++ ){
                userlimitOrderIds[_user][_index] = userlimitOrderIds[_user][_index+1];
            }
            userlimitOrderIds[_user].pop();
        }
        return idexisted;
    }
    function interSwap(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address tokenIn,
        uint256 amountIn,
        address tokenOut
    ) public onlyExecutor returns(uint buyAmt) {
        buyAmt = trade(executor,swapDataParam, swapProxy_index, tokenIn, amountIn, tokenOut);
        IStaking(staking).updateInterPool( tokenIn, amountIn, tokenOut, buyAmt );
    }
    function openPosition(
        address user,
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address tokenIn,
        uint256 amountIn,
        address tokenOut
    ) public nonReentrant returns (uint buyAmt)  {
        require(msg.sender == user || msg.sender == altexecutor[user], "caller has no permission");
        require(IStaking(staking).getTotalValueUsable(tokenIn) >= amountIn, "Total Usable Balance overflow");
        require(getTradableTokenAmt(user, tokenIn) >= amountIn, "User Tradable Balance overflow");
        
        uint256 _tradeInUSD = getAssetInUSD(tokenIn, amountIn);
        (bool pairCk, address _longtoken) = checkMarketPair(tokenIn, tokenOut);
        require(pairCk, "can't find the token pair");
        require(_tradeInUSD >= tradeLimit_Down, "trade amount can't be less than down limit");
        require(_tradeInUSD <= tradeLimit_Up[_longtoken], "trade amount can't be more than up limit");

        buyAmt = trade(user,swapDataParam, swapProxy_index, tokenIn, amountIn, tokenOut);
        IStaking(staking).updateTradeUsingAmt(tokenIn, amountIn, true); // increase the tradeUsingAmount

        // update the userinfo and total trade info
        tradeinfo[openId] = TradeInfo({
                id: openId,
                trader: user,
                tokenIn: tokenIn,
                amountIn: amountIn * (percentRate-tradeFeeRate) / percentRate,
                tokenOut: tokenOut,
                amountOut: buyAmt,
                updateTime: block.timestamp,
                feeAmount: 0,
                openPrice: IPriceOracle(priceoracle).getPrice(_longtoken),
                closePrice: 0,
                profitUSD: 0
            }
        );
        if(userOpenIds[user].length == 0){
            OpenedUsers.push(user);
        }
        userOpenIds[user].push(openId);
        openId ++;
        // }
    }
    function getOpenedUsers() public view returns( address[] memory ){
        return OpenedUsers;
    }
    function checkRepeatOpenState(address _user, address _tokenIn, address _tokenOut) internal view returns(uint256 _openId){
        uint256 len = userOpenIds[_user].length;
        bool isRepeated = false;
        for( uint256 _index = 0 ; _index < len ; _index++){
            if( tradeinfo[userOpenIds[_user][_index]].tokenIn ==  _tokenIn && tradeinfo[userOpenIds[_user][_index]].tokenOut ==  _tokenOut ){
                isRepeated = true;
                _openId = userOpenIds[_user][_index];
            }
        }
        if(!isRepeated){
            _openId = 1e18;
        }
    }
    function closeOpenId(
        address _user,
        uint256 _openId
    ) internal {
        uint256 len = userOpenIds[_user].length;
        uint256 _index;
        for( _index = 0 ; _index < len ; _index++){
            if(userOpenIds[_user][_index] == _openId){    
                break;
            }
        }
        for( ; _index < len - 1 ; _index++ ){
            userOpenIds[_user][_index] = userOpenIds[_user][_index+1];
        }
        userOpenIds[_user].pop();
        userCloseIds[_user].push(_openId);

        // if there is no opened position of the user, then delete the user from the OpenedUsers Array.
        if(userOpenIds[_user].length == 0){
            len = OpenedUsers.length;
            for( _index = 0 ; _index < len ; _index++){
                if(OpenedUsers[_index] == _user){
                    break;
                }
            }
            for( ; _index < len - 1 ; _index++ ){
                OpenedUsers[_index] = OpenedUsers[_index+1];
            }
            OpenedUsers.pop();
        }
    }
    function closeLimitOrderIdsByOpenIds(
        address _user,
        uint256 _openId
    ) internal {
        for(uint256 i = 0; i < userlimitOrderIds[_user].length;  ){
            uint256 _limitorderId = userlimitOrderIds[_user][i];
            bool removed = false;
            if(_openId == limitorderinfo[_limitorderId].openId){
                limitorderinfo[_limitorderId].status = false;
                removed = removeLimitOrderId(_user, _limitorderId);
            }
            if(!removed){
                i++;
            }
        }
    }
    function closeAllLimitOrderIds(
        address _user
    ) internal {
        while(userlimitOrderIds[_user].length > 0 ){
            uint256 _limitorderId = userlimitOrderIds[_user][userlimitOrderIds[_user].length-1];
            limitorderinfo[_limitorderId].status = false;
            userlimitOrderIds[_user].pop();
        }
    }
    function closeAllUserOpenIds(
        address _user
    ) internal {
        uint256 len = userOpenIds[_user].length;
        uint256 _index;
        for( _index = 0 ; _index < len ; _index++){
            closeOpenId(_user, userOpenIds[_user][userOpenIds[_user].length-1]);
        }
    }
    function closeAllPosition(
        bytes[] memory swapDataParam,
        uint256[] memory swapProxy_index
    ) public {
        require(swapDataParam.length == swapProxy_index.length && userOpenIds[msg.sender].length == swapProxy_index.length, "lengths are not matched");
        uint256 len = userOpenIds[msg.sender].length;
        for(uint256 i = 0 ; i < len ; i++ ){
            closePosition(swapDataParam[i], swapProxy_index[i], userOpenIds[msg.sender][i]);
        }
    }
    function closePosition(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        uint256 _openId
    ) public nonReentrant returns (uint backAmt)  {
        address trader = tradeinfo[_openId].trader;
        require(msg.sender == trader || msg.sender == altexecutor[trader],"caller has no permission");
        address _tokenIn = tradeinfo[_openId].tokenIn;
        uint256 _amountIn = tradeinfo[_openId].amountIn;
        address _tokenOut = tradeinfo[_openId].tokenOut;

        backAmt = trade(trader, swapDataParam, swapProxy_index, _tokenOut, tradeinfo[_openId].amountOut, _tokenIn);
        (, address _longtoken) = checkMarketPair(_tokenIn, _tokenOut);
        tradeinfo[_openId].closePrice = IPriceOracle(priceoracle).getPrice(_longtoken);
        tradeinfo[_openId].feeAmount = getFeeAmountById(_openId);
        uint256 leverageFee = tradeinfo[_openId].feeAmount;
        IStaking(staking).updateLockAmt(_tokenIn, leverageFee, true); // increase the staking lock amount
        IStaking(staking).updateTradeUsingAmt(_tokenIn, _amountIn, false); // decrease the total trade using amount
        tradeinfo[_openId].updateTime = block.timestamp;

        // profit = backAmt - _amountIn - leverageFee
        // collateral += profit
        if( backAmt >= _amountIn + leverageFee ){ // in the case of profit
            uint256 _profit = backAmt - _amountIn - leverageFee;
            IStaking(staking).tradeProfitsToCollateral(trader, _tokenIn, _profit);
            tradeinfo[_openId].profitUSD = int256(getAssetInUSD(_tokenIn, _profit));
        }
        else{ // in the case of loss
            uint256 _loss = _amountIn + leverageFee - backAmt;
            IStaking(staking).tradeLossToCollaterals(trader, _tokenIn, _loss);
            tradeinfo[_openId].profitUSD = int256(-1) * int256(getAssetInUSD(_tokenIn, _loss));
        }
        closeOpenId(trader, _openId);
        closeLimitOrderIdsByOpenIds(trader, _openId);
    }
    function getLiquidateUsers() public view returns(address[] memory){
        uint256 len = 0;
        for(uint256 i = 0 ; i < OpenedUsers.length ; i++){
            if(getTradableUSD(OpenedUsers[i]) == 0){
                len++;
            }
        }
        address[] memory _liquidateUsers = new address[](len);
        uint256 index = 0;
        for(uint256 i = 0 ; i < OpenedUsers.length ; i++){
            if(getTradableUSD(OpenedUsers[i]) == 0){
                _liquidateUsers[index++] = OpenedUsers[i];
            }
        }
        return _liquidateUsers;
    }
    function liquidatePosition(
        address[] memory users
    ) public onlyExecutor {
        require(msg.sender == executor, "no permission");
        for(uint256 _index = 0 ; _index < users.length ; _index++){
            address _user = users[_index];
            require(getTradableUSD(_user) == 0, "Liquidate Limit not arrived");
            for(uint256 i = 0 ; i < userOpenIds[_user].length; i++){
                uint256 _openId = userOpenIds[_user][i];
                address _tokenIn = tradeinfo[_openId].tokenIn;
                uint256 _amountIn = tradeinfo[_openId].amountIn;
                address _tokenOut = tradeinfo[_openId].tokenOut;
                uint256 _amountOut = tradeinfo[_openId].amountOut;
                tradeinfo[_openId].updateTime = block.timestamp;
                (, address _longtoken) = checkMarketPair(_tokenIn, _tokenOut);
                tradeinfo[_openId].closePrice = IPriceOracle(priceoracle).getPrice(_longtoken);
                tradeinfo[_openId].feeAmount = getFeeAmountById(_openId);
                tradeinfo[_openId].updateTime = block.timestamp;

                uint256 leverageFee = tradeinfo[_openId].feeAmount;
                IStaking(staking).updateLockAmt(_tokenIn, leverageFee, true); // increase the staking lock amount
                IStaking(staking).updateTradeUsingAmt(_tokenIn, _amountIn, false); // decrease the total trade using amount
                IStaking(staking).increasePoolSrcDstAmt(_tokenOut, _amountOut, true); // increasePoolSrcAmt
                IStaking(staking).increasePoolSrcDstAmt(_tokenIn, _amountIn+leverageFee, false); // increasePoolDstAmt

                tradeinfo[_openId].amountIn = 0;

            }
            IStaking(staking).liquidate(_user, true);
            closeAllUserOpenIds(_user);
            closeAllLimitOrderIds(_user);
        }
    }

    function getUSDInAsset( address _token, uint256 _amtUSD ) internal view returns(uint256 ){
        return _amtUSD * (10 ** IERC20(_token).decimals()) / IPriceOracle(priceoracle).getPrice(_token);
    }
    function getAssetInUSD( address _token, uint256 _amount ) internal view returns(uint256 ){
        return IPriceOracle(priceoracle).getPrice(_token) * _amount / (10 ** IERC20(_token).decimals());
    }
    function getCheckRemovableAmt( address _user, address _ctoken ) public view returns(uint256) {
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        uint256 _camtUSD = getTradableUSD(_user) / MAXMULTIPLY;
        
        uint256 _camt = getUSDInAsset(_ctoken, _camtUSD);
        uint256 _pid = IStaking(staking).getPidByToken(_ctoken);
        if(_userInfo[_pid].tradeCollateralAmt < _camt){
            _camt = _userInfo[_pid].tradeCollateralAmt;
        }
        if(getTradeInTokensUSD(_user)==0 && getTradeOutTokensUSD(_user)==0 && getOrderInTokenUSD(_user)==0){
            _camt = _userInfo[_pid].tradeCollateralAmt;
        }
        return  _camt;
    }
    function getCollateralRemovableAmt( address _user, address _ctoken ) public view returns(uint256) {
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        uint256 _camtUSD = getTradableUSD(_user) / MAXMULTIPLY;
        
        uint256 _camt = getUSDInAsset(_ctoken, _camtUSD);
        uint256 _pid = IStaking(staking).getPidByToken(_ctoken);
        if(_userInfo[_pid].tradeCollateralAmt < _camt){
            _camt = _userInfo[_pid].tradeCollateralAmt;
        }
        _camt = _camt * 90 / 100; // When trading, 90% of collateral can be withdrawable
        if(getTradeInTokensUSD(_user)==0 && getTradeOutTokensUSD(_user)==0 && getOrderInTokenUSD(_user)==0){
            _camt = _userInfo[_pid].tradeCollateralAmt;
        }
        return  _camt;
    }
    function getCollateralRemovableAmtList( address _user ) public view returns(uint256[] memory ) {
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        uint256[] memory _amountArray = new uint256[](_userInfo.length);
        for( uint256 i = 0 ; i < _userInfo.length ; i++ ){
            _amountArray[i] = getCollateralRemovableAmt(_user, _userInfo[i].token);
        }
        return _amountArray;
    }
    function getTradableUSD(address _user) public view returns(uint256 _amountUSD){
        // profit =  amountOutUSD - amountInUSD - usingFee
        _amountUSD = 0;
        if(getCollateralsInUSD(_user) + getTradeOutTokensUSD(_user) > getTradeInTokensUSD(_user) + getFeeAmountUSDByUser(_user)){ 
            if((getCollateralsInUSD(_user) + getTradeOutTokensUSD(_user) - getTradeInTokensUSD(_user) - getFeeAmountUSDByUser(_user)) * MAXMULTIPLY > getOrderInTokenUSD(_user) + getTradeInTokensUSD(_user)){
                _amountUSD = (getCollateralsInUSD(_user) + getTradeOutTokensUSD(_user) - getTradeInTokensUSD(_user) - getFeeAmountUSDByUser(_user)) * MAXMULTIPLY - getOrderInTokenUSD(_user) - getTradeInTokensUSD(_user);
            }
        }
    }
    function getCurrentProfitUSD(address _user) public view returns(int256 pnl){
        pnl = int256(getTradeOutTokensUSD(_user)) - int256(getTradeInTokensUSD(_user)) - int256(getFeeAmountUSDByUser(_user));
    }
    function getTradableTokenAmt( address _user, address _token ) public view returns(uint256 _camt) {
        uint256 _amountInUSD = getTradableUSD(_user);
        _camt = getUSDInAsset(_token, _amountInUSD);
    }
    function getTradableAmtList( address _user ) public view returns(uint256[] memory) {
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        uint256[] memory _amountArray = new uint256[](_userInfo.length);
        for( uint256 i = 0 ; i < _userInfo.length ; i++ ){
            _amountArray[i] = getTradableTokenAmt(_user, _userInfo[i].token);
        }
        return _amountArray;
    }
    // function getTraderProfit(address _user)
    function getCollateralsInUSD(address _user) public view returns(uint256){
        uint256 _amtUSD = 0;
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        for( uint256 i = 0 ; i < _userInfo.length ; i++ ){
            _amtUSD += getAssetInUSD( _userInfo[i].token,_userInfo[i].tradeCollateralAmt);
        }
        return _amtUSD;
    }
    function getTradeInTokensUSD(address _user) public view returns(uint256){
        uint256 _amtUSD = 0;
        TradeInfo[] memory _tradeInfo = getTradeInfo(_user);
        for(uint256 i = 0; i < _tradeInfo.length; i++ ){
            _amtUSD += getAssetInUSD( _tradeInfo[i].tokenIn, _tradeInfo[i].amountIn );
        }
        return _amtUSD;
    }
    function getOrderInTokenUSD(address _user) internal view returns(uint256){
        uint256 _amtUSD = 0;
        for(uint256 i = 0; i < userlimitOrderIds[_user].length; i++ ){
            uint256 _limitOrderId = userlimitOrderIds[_user][i];
            if( limitorderinfo[_limitOrderId].openPerform == false || limitorderinfo[_limitOrderId].status == false){
                continue;
            }
            _amtUSD += getAssetInUSD( limitorderinfo[_limitOrderId].tokenIn, limitorderinfo[_limitOrderId].amountIn );
        }
        return _amtUSD;
    }
    function getLimitOrderInfo(address _user) public view returns(LimitOrderInfo[] memory){
        LimitOrderInfo[] memory _limitorderInfo = new LimitOrderInfo[](userlimitOrderIds[_user].length);
        for(uint256 i = 0; i < userlimitOrderIds[_user].length; i++ ){
            uint256 _limitorderId = userlimitOrderIds[_user][i];
            if(!limitorderinfo[_limitorderId].status){
                continue;
            }
            _limitorderInfo[i] = LimitOrderInfo({
                user: _user,
                orderTime: limitorderinfo[_limitorderId].orderTime,
                limitorderId: _limitorderId,
                tokenIn: limitorderinfo[_limitorderId].tokenIn,
                amountIn: limitorderinfo[_limitorderId].amountIn,
                tokenOut: limitorderinfo[_limitorderId].tokenOut,
                indexToken: limitorderinfo[_limitorderId].indexToken,
                indexAmount: limitorderinfo[_limitorderId].indexAmount,
                indexUSD: limitorderinfo[_limitorderId].indexUSD,
                limitPrice: limitorderinfo[_limitorderId].limitPrice,
                upPrice: limitorderinfo[_limitorderId].upPrice,
                downPrice: limitorderinfo[_limitorderId].downPrice,
                highStart: limitorderinfo[_limitorderId].highStart,
                openPerform: limitorderinfo[_limitorderId].openPerform,
                openId: limitorderinfo[_limitorderId].openId,
                status: limitorderinfo[_limitorderId].status
            });
        }
        return _limitorderInfo;
    }
    function getTradeOutTokensUSD(address _user) internal view returns(uint256){
        uint256 _amtUSD = 0;
        TradeInfo[] memory _tradeInfo = getTradeInfo(_user);
        for(uint256 i = 0; i < _tradeInfo.length; i++ ){
            _amtUSD += getAssetInUSD( _tradeInfo[i].tokenOut, _tradeInfo[i].amountOut );
        }
        return _amtUSD;
    }
    function getTradeInfo(address _user) public view returns(TradeInfo[] memory){
        TradeInfo[] memory _tradeInfo = new TradeInfo[](userOpenIds[_user].length);
        for(uint256 i = 0; i < userOpenIds[_user].length; i++){
            uint256 _openId = userOpenIds[_user][i];
            _tradeInfo[i] = TradeInfo({
                id: _openId,
                trader: _user,
                tokenIn: tradeinfo[_openId].tokenIn,
                amountIn: tradeinfo[_openId].amountIn,
                tokenOut: tradeinfo[_openId].tokenOut,
                amountOut: tradeinfo[_openId].amountOut,
                updateTime: tradeinfo[_openId].updateTime,
                feeAmount: getFeeAmountById(_openId),
                openPrice: tradeinfo[_openId].openPrice,
                closePrice: tradeinfo[_openId].openPrice,
                profitUSD: tradeinfo[_openId].profitUSD
            });
        }
        return _tradeInfo;
    }
    function getTradeCloseInfo(address _user) public view returns(TradeCloseInfo[] memory){
        TradeCloseInfo[] memory _tradeInfo = new TradeCloseInfo[](userCloseIds[_user].length);
        for(uint256 i = 0; i < userCloseIds[_user].length; i++){
            uint256 _openId = userCloseIds[_user][i];
            (, address _indexToken) = checkMarketPair(tradeinfo[_openId].tokenIn, tradeinfo[_openId].tokenOut);
            bool _tradetype;
            uint256 _indexAmount;
            if(_indexToken == tradeinfo[_openId].tokenOut){
                _tradetype = true;
                _indexAmount = tradeinfo[_openId].amountOut;
            }
            else{
                _tradetype = false;
                _indexAmount = tradeinfo[_openId].amountIn;
            }
            _tradeInfo[i] = TradeCloseInfo({
                id: _openId,
                trader: _user,
                tradetype: _tradetype,
                indexToken: _indexToken,
                indexAmount: _indexAmount,
                indexUSD: getAssetInUSD(_indexToken, _indexAmount),
                closeTime: tradeinfo[_openId].updateTime,
                openPrice: tradeinfo[_openId].openPrice,
                closePrice: tradeinfo[_openId].closePrice,
                profitUSD: tradeinfo[_openId].profitUSD
            });
        }
        return _tradeInfo;
    }
    function getTradeDetailInfo(address _user) public view returns(TradeDetailInfo[] memory){
        TradeDetailInfo[] memory _tradeInfo = new TradeDetailInfo[](userOpenIds[_user].length);
        for(uint256 i = 0; i < userOpenIds[_user].length; i++){
            uint256 _openId = userOpenIds[_user][i];
            uint256 _amountOut = tradeinfo[_openId].amountOut;
            (, address _indexToken) = checkMarketPair(tradeinfo[_openId].tokenIn, tradeinfo[_openId].tokenOut);
            bool _tradetype;
            uint256 _indexAmount;
            address _stableToken;
            uint256 _stableAmount;
            if(_indexToken == tradeinfo[_openId].tokenOut){
                _tradetype = true;
                _indexAmount = tradeinfo[_openId].amountOut;
                _stableToken = tradeinfo[_openId].tokenIn;
                _stableAmount = tradeinfo[_openId].amountIn;
            }
            else{
                _tradetype = false;
                _indexAmount = tradeinfo[_openId].amountIn;
                _stableToken = tradeinfo[_openId].tokenOut;
                _stableAmount = _amountOut;
            }

            // uint256 _removableAmt = getCollateralRemovableAmt(_user, _indexToken);
            uint256 _removableUSD = getTradableUSD(_user) / MAXMULTIPLY;
            uint256 _onTradeUSD = getAssetInUSD(tradeinfo[_openId].tokenIn, tradeinfo[_openId].amountIn);
            uint256 _liqPrice = IPriceOracle(priceoracle).getPrice(_indexToken);
            if(_tradetype){
                if(_removableUSD >= _onTradeUSD){
                    _liqPrice = 0;
                }
                else{
                    _liqPrice = (_onTradeUSD - _removableUSD) * _liqPrice / _onTradeUSD;
                }
            }
            else{
                if(_onTradeUSD == 0){
                    _liqPrice = 0;
                }
                else{
                    _liqPrice = (_onTradeUSD + _removableUSD) * _liqPrice / _onTradeUSD;
                }
            }

            _tradeInfo[i] = TradeDetailInfo({
                id: _openId,
                trader: _user,
                tradetype: _tradetype,
                indexToken: _indexToken,
                indexAmount: _indexAmount,
                stableToken: _stableToken,
                stableAmount: _stableAmount,
                indexUSD: getAssetInUSD(_indexToken, _indexAmount),
                entryPrice: tradeinfo[_openId].openPrice,
                marketPrice: IPriceOracle(priceoracle).getPrice(_indexToken),
                liqPrice: _liqPrice,
                feeAmount: getFeeAmountById(_openId),
                feeUSD: getAssetInUSD(_indexToken, getFeeAmountById(_openId))
            });
        }
        return _tradeInfo;
    }
    function getFeeAmountById(uint256 _openId) internal view returns(uint256 feeAmount){
        feeAmount = tradeinfo[_openId].feeAmount;
        uint256 tradePeriod = block.timestamp - tradeinfo[_openId].updateTime;
        feeAmount += (tradePeriod * tradeinfo[_openId].amountIn * tradeapr / percentRate / feePeriod);
    }
    function getFeeAmountUSDByUser(address _user) public view returns(uint256){
        uint256 feeSum = 0;
        for( uint256 i = 0 ; i < userOpenIds[_user].length ; i ++){
            uint256 _openId = userOpenIds[_user][i];
            uint256 _amount = getFeeAmountById(_openId);
            address _token = tradeinfo[_openId].tokenIn;
            feeSum += getAssetInUSD(_token, _amount);
        }
        return feeSum;
    }
    function checkMarketPair(address _token1, address _token2) internal view returns(bool _flg, address _longtoken){
        _flg = false;
        for(uint i =  0; i < marketpair.length; i++){
            if( marketpair[i].longtoken == _token1 && marketpair[i].shorttoken == _token2 ){
                _flg = true;
                _longtoken = _token1;
                break;
            }
            if( marketpair[i].longtoken == _token2 && marketpair[i].shorttoken == _token1 ){
                _flg = true;
                _longtoken = _token2;
                break;
            }
        }
    }
    
    receive() external payable {
        assert(msg.sender == weth); // only accept ETH via fallback from the WETH contract
    }
}
