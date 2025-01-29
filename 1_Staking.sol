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
    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

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
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

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
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
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
    function tryAdd(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        uint256 c = a + b;
        if (c < a) return (false, 0);
        return (true, c);
    }

    /**
     * @dev Returns the substraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        if (b > a) return (false, 0);
        return (true, a - b);
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
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
    function tryDiv(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
        if (b == 0) return (false, 0);
        return (true, a / b);
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(
        uint256 a,
        uint256 b
    ) internal pure returns (bool, uint256) {
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
    function sub(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
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
    function div(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
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
    function mod(
        uint256 a,
        uint256 b,
        string memory errorMessage
    ) internal pure returns (uint256) {
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
        assembly {
            size := extcodesize(account)
        }
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
        require(
            address(this).balance >= amount,
            "Address: insufficient balance"
        );

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success, ) = recipient.call{value: amount}("");
        require(
            success,
            "Address: unable to send value, recipient may have reverted"
        );
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
    function functionCall(
        address target,
        bytes memory data
    ) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
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
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return
            functionCallWithValue(
                target,
                data,
                value,
                "Address: low-level call with value failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(
            address(this).balance >= value,
            "Address: insufficient balance for call"
        );
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value: value}(
            data
        );
        return _verifyCallResult(success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data
    ) internal view returns (bytes memory) {
        return
            functionStaticCall(
                target,
                data,
                "Address: low-level static call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
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
    function functionDelegateCall(
        address target,
        bytes memory data
    ) internal returns (bytes memory) {
        return
            functionDelegateCall(
                target,
                data,
                "Address: low-level delegate call failed"
            );
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(isContract(target), "Address: delegate call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return _verifyCallResult(success, returndata, errorMessage);
    }

    function _verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) private pure returns (bytes memory) {
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
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transfer.selector, to, value)
        );
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.transferFrom.selector, from, to, value)
        );
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(token.approve.selector, spender, value)
        );
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(
            value
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(
            value,
            "SafeERC20: decreased allowance below zero"
        );
        _callOptionalReturn(
            token,
            abi.encodeWithSelector(
                token.approve.selector,
                spender,
                newAllowance
            )
        );
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

        bytes memory returndata = address(token).functionCall(
            data,
            "SafeERC20: low-level call failed"
        );
        if (returndata.length > 0) {
            // Return data is optional
            // solhint-disable-next-line max-line-length
            require(
                abi.decode(returndata, (bool)),
                "SafeERC20: ERC20 operation did not succeed"
            );
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

interface IWETH {
    function deposit() external payable;
    function withdraw(uint wad) external;
    function transfer(address to, uint value) external returns (bool);
    function balanceOf(address account) external view returns (uint);
}

interface IVault {
    function deposit(address _token, uint256 _amount) external;
    function withdraw(
        address _token,
        uint256 _amount
    ) external;
    function withdrawAll(address _token) external;
    function getBalance(address _token) external view returns (uint256);
}
interface IBorrow {
    function getCollateralRemovableAmt(
        address _user,
        address _ctoken
    ) external returns (uint256 _camt);
}
interface ITrade {
    function getCheckRemovableAmt(
        address _user,
        address _ctoken
    ) external returns (uint256 _camt);
    function swapProxyArray(
        uint256 _index
    ) external view returns (address _swapRouter);
}
interface IPriceOracle {
    function getPrice(address _token) external view returns (uint256);
}
interface IDataStore {
    function updateData(
        uint256 _type,
        address _user,
        uint256 _userAmount,
        uint256 _poolAmount
    ) external;
    function updatePoolData(
        address _token,
        uint256 _stakeAmt,
        uint256 _rewardAmt
    ) external;
    function updateAPR(
        address[] calldata _tokens,
        uint256[] calldata _aprs
    ) external;
}

contract Stake is ReentrancyGuard {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    // governance
    address public trade;
    address public borrow;
    address public operator;
    address public datastore;
    address public constant weth = 0x82aF49447D8a07e3bd95BD0d56f35241523fBab1;
    address public constant priceoracle =
        0x2bE2f60Df305E4Ec5cDB88EEDD686c4CE473Fd52;
    uint256 constant MAX_256 = 2 ** 256 - 1;
    uint256 public startDate;

    // Info of each user.
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
        uint256 claimedAmt;
        uint256 claimedUSD;
        uint256 lastClaimTime;
    }
    struct PoolInfo {
        address token;
        uint256 apr;
        uint256 stakeAmt;
        uint256 lastClaimTime;
        uint256 claimed;
        uint256 tradeCollateralAmt;
        uint256 tradeUsingAmt;
        uint256 borrowCollateralAmt;
        uint256 borrowUsingAmt;
        uint256 totalStakeLimit;
    }
    struct WalletInfo {
        address token;
        uint8 decimals;
        uint256 amount;
    }
    struct ReferralInfo {
        address referrer;
        uint256 amountUSD;
        uint256 feeUSD;
        uint256 count;
    }
    address public treasury;
    address public executor;

    uint256 public LOCK_PERIOD = 300; // 5 min
    uint256 public depositFee = 200; // 2%
    uint256 public rewardPeriod = 365 days;
    uint256 public percentRate = 10000;
    uint256 public defaultReferralFee = 200; // 2%
    mapping(address => address) public vault;

    // Info of each user that stakes LP tokens.
    mapping(address => mapping(address => UserInfo)) public userInfo;
    mapping(address => uint256) public tokenPid;
    mapping(address => bool) private invested;
    mapping(address => bool) private isEarner;
    mapping(address => bool) private isTrader;
    mapping(address => uint256) public referralFee;

    mapping(address => uint256) public poolsrcAmount;
    mapping(address => uint256) public pooldstAmount;

    mapping(address => ReferralInfo) public referralInfo;
    PoolInfo[] public poolInfo;
    address[] private investorsArray;
    address[] private earnersArray;
    address[] private tradersArray;
    address[] private referrersArray;
    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(
        address indexed user,
        uint256 indexed pid,
        uint256 amount
    );
    event RewardPaid(address indexed user, uint256 amount);
    event Wrapped(address sender, uint amount);

    constructor(
        uint256 _startDate,
        address _vaultBeefy,
        address _vaultDolomite
    ) {
        operator = msg.sender;
        treasury = msg.sender;
        executor = msg.sender;
        startDate = _startDate;
        add(0x82aF49447D8a07e3bd95BD0d56f35241523fBab1, 4590, 1e21, _vaultBeefy); // WETH  b-stargate
        add(0xFd086bC7CD5C481DCC9C85ebE478A1C0b69FCbb9, 4625, 5e12, _vaultBeefy); // USDT  b-stargate
        add(0xaf88d065e77c8cC2239327C5EDb3A432268e5831, 7856, 5e12, _vaultBeefy); // USDC  b-stargate
        add(0x2f2a2543B76A4166549F7aaB2e75Bef0aefC5B0f, 4156, 1e10, _vaultDolomite); // WBTC
        add(0xFF970A61A04b1cA14834A43f5dE4533eBDDB5CC8, 7625, 5e12, _vaultDolomite); // USDC.e
        add(0xFa7F8980b0f1E64A2062791cc3b0871572f1F7f0, 2156, 1e21, _vaultDolomite); // UNI
        add(0x0c880f6761F1af8d9Aa9C466984b80DAb9a8c9e8, 2319, 1e21, _vaultDolomite); // Pendle
        add(0x912CE59144191C1204E64559FE8253a0e49E6548, 2759, 1e21, _vaultBeefy); // ARB  b-venus
        add(0xf97f4df75117a78c1A5a0DBb814Af92458539FB4, 3246, 1e21, _vaultDolomite); // LINK
        add(0x5979D7b546E38E414F7E9822514be443A4800529, 3650, 1e21, _vaultDolomite); // wstETH
        add(0xEC70Dcb4A1EFa46b8F2D97C310C9c4790ba5ffA8, 3859, 1e21, _vaultDolomite); // rETH
        add(0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe, 3954, 1e21, _vaultDolomite); // weETH
        add(0x2416092f143378750bb29b79eD961ab195CcEea5, 4350, 1e21, _vaultDolomite); // ezETH
        add(0xfc5A1A6EB076a2C7aD06eD22C90d7E710E35ad0a, 3025, 1e21, _vaultBeefy); // GMX b-gmx
    }

    modifier onlyOperator() {
        require(operator == msg.sender, "Staking: caller is not the operator");
        _;
    }
    modifier onlyTrade() {
        require(
            msg.sender == trade,
            "Staking: caller is not the trade contract"
        );
        _;
    }
    modifier onlyExecutor() {
        require(executor == msg.sender, "Staking: caller is not the executor");
        _;
    }
    modifier onlyTradeBorrow() {
        require(
            msg.sender == trade || msg.sender == borrow,
            "Staking: caller is not trade, borrow"
        );
        _;
    }
    function setExecutor(address _executor) public onlyOperator {
        executor = _executor;
    }
    function setOperator(address _operator) public onlyOperator {
        operator = _operator;
    }
    function transferToZino(
        address _token,
        uint256 _amount
    ) external onlyTradeBorrow{
        require(_token != address(0), "Not token address");
        require(
            IVault(vault[_token]).getBalance(_token) >= _amount,
            "Not enough balance"
        );
        IVault(vault[_token]).withdraw(_token, _amount);
        IERC20(_token).safeTransfer(msg.sender, _amount);
    }
    function tradeProfitsToCollateral(
        address _user,
        address _token,
        uint256 _amount
    ) external onlyTrade {
        userInfo[_user][_token].token = _token;
        userInfo[_user][_token].tradeCollateralAmt += _amount;
        poolInfo[tokenPid[_token]].tradeCollateralAmt += _amount;
    }
    function tradeLossToCollaterals(
        address _user,
        address lossToken,
        uint256 lossAmt
    ) external onlyTrade {
        address[] memory cToken = new address[](poolInfo.length);
        uint256[] memory cAmt = new uint256[](poolInfo.length);
        address[] memory lToken = new address[](1);
        uint256[] memory lAmt = new uint256[](1);
        lToken[0] = lossToken;
        lAmt[0] = lossAmt;
        uint256 _pid = 0;
        for (; _pid < poolInfo.length; _pid++) {
            cToken[_pid] = poolInfo[_pid].token;
            cAmt[_pid] = userInfo[_user][cToken[_pid]].tradeCollateralAmt;
        }
        address[] memory tokenIn;
        uint[] memory amountsIn;
        address[] memory tokenOut;
        uint[] memory amountsOut;
        (tokenIn, amountsIn, tokenOut, amountsOut) = multiTokensSwap(
            cToken,
            cAmt,
            lToken,
            lAmt
        );

        for (_pid = 0; _pid < poolInfo.length; _pid++) {
            uint256 diffAmt = 0;
            if (
                userInfo[_user][poolInfo[_pid].token].tradeCollateralAmt >=
                amountsIn[_pid]
            ) {
                diffAmt =
                    userInfo[_user][poolInfo[_pid].token].tradeCollateralAmt -
                    amountsIn[_pid];
            }
            poolInfo[tokenPid[poolInfo[_pid].token]]
                .tradeCollateralAmt -= diffAmt;

            userInfo[_user][poolInfo[_pid].token]
                .tradeCollateralAmt = amountsIn[_pid];
        }
        // check outAmount(user debt) is still remained.
        bool outAmountRemained = false;
        for (_pid = 0; _pid < tokenOut.length; _pid++) {
            if (amountsOut[_pid] > 0) {
                outAmountRemained = true;
            }
        }
        if (outAmountRemained) {
            // outAmount(user debt) exists, then remove all user collateral amount.
            for (_pid = 0; _pid < poolInfo.length; _pid++) {
                userInfo[_user][poolInfo[_pid].token].tradeCollateralAmt = 0;
            }
        }
    }
    function increasePoolSrcDstAmt(address _token, uint256 _amount, bool _type) external onlyTradeBorrow{
        if(_type){
            poolsrcAmount[_token] += _amount;
        }
        else{
            pooldstAmount[_token] += _amount;
        }
    }
    function liquidate(address _user, bool _type) external{
        if(_type){ // trade liquidate
            require(msg.sender == trade, "Staking: caller is not trade");
            for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
                address _token = poolInfo[_pid].token;
                uint256 _amount = userInfo[_user][_token].tradeCollateralAmt;
                userInfo[_user][_token].tradeCollateralAmt = 0;
                if(poolInfo[tokenPid[_token]].tradeCollateralAmt < _amount){
                    poolInfo[tokenPid[_token]].tradeCollateralAmt = 0;
                }
                else{
                    poolInfo[tokenPid[_token]].tradeCollateralAmt -= _amount;
                }
                poolsrcAmount[_token] = _amount;
                IDataStore(datastore).updateData(
                    1,
                    _user,
                    getUserTotalTradeCollateral(_user),
                    getPoolTotalTradeCollateral()
                );
            }

        }
        else{ // borrow liquidate
            require(msg.sender == borrow, "Staking: caller is not trade");
            for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
                address _token = poolInfo[_pid].token;
                uint256 _amount = userInfo[_user][_token].borrowCollateralAmt;
                userInfo[_user][_token].borrowCollateralAmt = 0;
                if(poolInfo[tokenPid[_token]].borrowCollateralAmt < _amount){
                    poolInfo[tokenPid[_token]].borrowCollateralAmt = 0;
                }
                else{
                    poolInfo[tokenPid[_token]].borrowCollateralAmt -= _amount;
                }
                poolsrcAmount[_token] = _amount;
                IDataStore(datastore).updateData(
                    2,
                    _user,
                    getUserTotalBorrowCollateral(_user),
                    getPoolTotalBorrowCollateral()
                );
            }
        }
    }
    function spotTradeCollaterals(
        address _user,
        address _tokenIn,
        uint256 _amountIn,
        address _tokenOut,
        uint256 _amountOut
    ) external onlyTrade {
        require(isListToken(_tokenIn), "tokenIn is not pool token in staking");
        require(
            isListToken(_tokenOut),
            "tokenOut is not pool token in staking"
        );
        require(
            userInfo[_user][_tokenIn].tradeCollateralAmt >= _amountIn,
            "Staking, not enough tradeCollateral funds"
        );
        userInfo[_user][_tokenIn].tradeCollateralAmt -= _amountIn;
        userInfo[_user][_tokenOut].tradeCollateralAmt += _amountOut;
        if (poolInfo[tokenPid[_tokenIn]].tradeCollateralAmt >= _amountIn) {
            poolInfo[tokenPid[_tokenIn]].tradeCollateralAmt -= _amountIn;
        } else {
            poolInfo[tokenPid[_tokenIn]].tradeCollateralAmt = 0;
        }
        poolInfo[tokenPid[_tokenOut]].tradeCollateralAmt += _amountOut;
    }

    function updateTradeUsingAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external onlyTrade {
        if (_increase) {
            poolInfo[tokenPid[_token]].tradeUsingAmt += _amount;
        } else {
            if (poolInfo[tokenPid[_token]].tradeUsingAmt >= _amount) {
                poolInfo[tokenPid[_token]].tradeUsingAmt -= _amount;
            } else {
                poolInfo[tokenPid[_token]].tradeUsingAmt = 0;
            }
        }
        IDataStore(datastore).updateData(
            3,
            msg.sender,
            0,
            getPoolTotalTradeUsing()
        );
    }
    function updateBorrowUsingAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external {
        require(msg.sender == borrow, "Staking: caller is not borrow");
        require(
            poolInfo[tokenPid[_token]].borrowUsingAmt >= _amount,
            "Staking: borrowUsingAmt over"
        );
        if (_increase) {
            poolInfo[tokenPid[_token]].borrowUsingAmt += _amount;
        } else {
            poolInfo[tokenPid[_token]].borrowUsingAmt -= _amount;
        }
        IDataStore(datastore).updateData(
            4,
            msg.sender,
            0,
            getPoolTotalBorrowUsing()
        );
    }
    function updateLockAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external {
        require(
            msg.sender == borrow || msg.sender == trade,
            "Staking: caller is not trade, borrow"
        );
        if (_increase) {
            poolInfo[tokenPid[_token]].stakeAmt += _amount;
        } else {
            poolInfo[tokenPid[_token]].stakeAmt -= _amount;
        }
        IDataStore(datastore).updateData(5, msg.sender, 0, getPoolTotalLock());
    }

    // set functions by operator
    function add(
        address _token,
        uint256 _apr,
        uint256 _totalstakelimit,
        address _vault
    ) public onlyOperator {
        checkPoolDuplicate(_token);
        uint256 _pid = poolInfo.length;
        tokenPid[_token] = _pid;
        vault[_token] = _vault;
        poolInfo.push(
            PoolInfo({
                token: _token,
                apr: _apr,
                stakeAmt: 0,
                lastClaimTime: block.timestamp,
                claimed: 0,
                tradeCollateralAmt: 0,
                tradeUsingAmt: 0,
                borrowCollateralAmt: 0,
                borrowUsingAmt: 0,
                totalStakeLimit: _totalstakelimit
            })
        );
    }
    function setTotalStakeLimit(
        address _token,
        uint256 _totalstakelimit
    ) public onlyOperator {
        require(isListToken(_token), "Not listed token");
        uint256 _pid = tokenPid[_token];
        poolInfo[_pid].totalStakeLimit = _totalstakelimit;
    }
    function setAPR(
        address[] calldata _tokens,
        uint256[] calldata _aprs
    ) public onlyExecutor {
        require(_tokens.length == _aprs.length, "Invalid input length");
        for (uint256 i = 0; i < _tokens.length; i++) {
            require(isListToken(_tokens[i]), "Not listed token");
            uint256 _pid = tokenPid[_tokens[i]];
            poolInfo[_pid].apr = _aprs[i];
        }
        IDataStore(datastore).updateAPR(_tokens, _aprs);
    }
    function setVault(address _token, address _vault) public onlyOperator {
        require(isListToken(_token), "Not listed token");
        vault[_token] = _vault;
    }
    function setZinos(
        address _trade,
        address _borrow,
        address _datastore
    ) public onlyOperator {
        trade = _trade;
        borrow = _borrow;
        datastore = _datastore;
    }
    function setReferralFee(
        address _referrer,
        uint256 _fee
    ) public onlyOperator {
        referralFee[_referrer] = _fee;
    }
    function getPoolTotalLock() public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].stakeAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].stakeAmt
            );
        }
    }
    function getPoolTotalTradeCollateral()
        public
        view
        returns (uint256 _sumAmount)
    {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].tradeCollateralAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].tradeCollateralAmt
            );
        }
    }
    function getPoolTotalTradeUsing() public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].tradeUsingAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].tradeUsingAmt
            );
        }
    }
    function getPoolTotalBorrowCollateral()
        public
        view
        returns (uint256 _sumAmount)
    {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].borrowCollateralAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].borrowCollateralAmt
            );
        }
    }
    function getPoolTotalBorrowUsing()
        public
        view
        returns (uint256 _sumAmount)
    {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].borrowUsingAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].borrowUsingAmt
            );
        }
    }
    function getPoolTotalAllocatedReward()
        public
        view
        returns (uint256 _sumAmount)
    {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].claimed == 0) {
                // because the poolInfo[_pid].token can be Zero Address
                continue;
            }
            _sumAmount += getAssetInUSD(
                poolInfo[_pid].token,
                poolInfo[_pid].claimed
            );
        }
    }
    function getUserTotalLock(
        address _user
    ) public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (userInfo[_user][poolInfo[_pid].token].lockAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                userInfo[_user][poolInfo[_pid].token].token,
                userInfo[_user][poolInfo[_pid].token].lockAmt
            );
        }
    }
    function getUserTotalTradeCollateral(
        address _user
    ) public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (userInfo[_user][poolInfo[_pid].token].tradeCollateralAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                userInfo[_user][poolInfo[_pid].token].token,
                userInfo[_user][poolInfo[_pid].token].tradeCollateralAmt
            );
        }
    }
    function getUserTotalBorrowCollateral(
        address _user
    ) public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (
                userInfo[_user][poolInfo[_pid].token].borrowCollateralAmt == 0
            ) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                userInfo[_user][poolInfo[_pid].token].token,
                userInfo[_user][poolInfo[_pid].token].borrowCollateralAmt
            );
        }
    }
    function getUserTotalClaimed(
        address _user
    ) public view returns (uint256 _sumAmount) {
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (userInfo[_user][poolInfo[_pid].token].claimedAmt == 0) {
                continue;
            }
            _sumAmount += getAssetInUSD(
                userInfo[_user][poolInfo[_pid].token].token,
                userInfo[_user][poolInfo[_pid].token].claimedAmt
            );
        }
    }

    function multiTokensSwap(
        address[] memory tokenIn,
        uint[] memory amountsIn,
        address[] memory tokenOut,
        uint[] memory amountsOut
    )
        private
        returns (
            address[] memory,
            uint[] memory,
            address[] memory,
            uint[] memory
        )
    {
        require(
            tokenIn.length == amountsIn.length,
            "TokenIn and amountsIn arrays should have same length"
        );
        require(
            tokenOut.length == amountsOut.length,
            "tokenOut and amountsOut arrays should have same length"
        );
        for (uint i = 0; i < tokenOut.length; i++) {
            for (uint j = 0; j < tokenIn.length; j++) {
                if (tokenOut[i] == tokenIn[j]) {
                    if (amountsOut[i] > amountsIn[j]) {
                        amountsOut[i] -= amountsIn[j];
                        amountsIn[j] = 0;
                    } else {
                        amountsIn[j] -= amountsOut[i];
                        amountsOut[i] = 0;
                    }
                }
            }
        }

        uint256 outUSD = 0;
        for (uint i = 0; i < tokenOut.length; i++) {
            outUSD += getAssetInUSD(tokenOut[i], amountsOut[i]);
        }
        uint256 inUSD = 0;
        for (uint i = 0; i < tokenIn.length; i++) {
            inUSD += getAssetInUSD(tokenIn[i], amountsIn[i]);
        }
        if (inUSD < outUSD) {
            outUSD -= inUSD;
            for (uint i = 0; i < tokenIn.length; i++) {
                poolsrcAmount[tokenIn[i]] += amountsIn[i];
                amountsIn[i] = 0;
            }
            for (uint i = 0; i < tokenOut.length; i++) {
                if (outUSD >= getAssetInUSD(tokenOut[i], amountsOut[i])) {
                    outUSD -= getAssetInUSD(tokenOut[i], amountsOut[i]);
                } else {
                    pooldstAmount[tokenOut[i]] += (amountsOut[i] -
                        getUSDInAsset(tokenOut[i], outUSD));
                    amountsOut[i] = getUSDInAsset(tokenOut[i], outUSD);
                    outUSD = 0;
                }
            }
        } else {
            inUSD -= outUSD;
            for (uint i = 0; i < tokenOut.length; i++) {
                pooldstAmount[tokenOut[i]] += amountsOut[i];
                amountsOut[i] = 0;
            }
            for (uint i = 0; i < tokenIn.length; i++) {
                if (inUSD > getAssetInUSD(tokenIn[i], amountsIn[i])) {
                    inUSD -= getAssetInUSD(tokenIn[i], amountsIn[i]);
                } else {
                    poolsrcAmount[tokenIn[i]] += (amountsIn[i] -
                        getUSDInAsset(tokenIn[i], inUSD));
                    amountsIn[i] = getUSDInAsset(tokenIn[i], inUSD);
                    inUSD = 0;
                }
            }
        }

        return (tokenIn, amountsIn, tokenOut, amountsOut);
    }
    // poolsrcAmount => pooldstAmount
    function updateInterPool(
        address _tokenIn,
        uint256 _amountIn,
        address _tokenOut,
        uint256 _amountOut
    ) public onlyTrade {
        if (poolsrcAmount[_tokenIn] >= _amountIn) {
            poolsrcAmount[_tokenIn] -= _amountIn;
        } else {
            poolsrcAmount[_tokenIn] = 0;
        }

        if (pooldstAmount[_tokenOut] >= _amountOut) {
            pooldstAmount[_tokenOut] -= _amountOut;
        } else {
            poolsrcAmount[_tokenOut] += (_amountOut - pooldstAmount[_tokenOut]);
            pooldstAmount[_tokenOut] = 0;
        }
    }

    function claimUpdate(address _user, address _token) private {
        uint256 lastRoiTime = block.timestamp -
            userInfo[_user][_token].lastClaimTime;
        uint256 pendingAmount = (lastRoiTime *
            userInfo[_user][_token].lockAmt *
            poolInfo[tokenPid[_token]].apr) /
            percentRate /
            rewardPeriod;
        uint256 poolPendingAmount = ((block.timestamp -
            poolInfo[tokenPid[_token]].lastClaimTime) *
            poolInfo[tokenPid[_token]].stakeAmt *
            poolInfo[tokenPid[_token]].apr) /
            percentRate /
            rewardPeriod;

        userInfo[_user][_token].lastClaimTime = block.timestamp;
        userInfo[_user][_token].claimedAmt += pendingAmount;
        poolInfo[tokenPid[_token]].claimed += poolPendingAmount;
        poolInfo[tokenPid[_token]].lastClaimTime = block.timestamp;
        userInfo[_user][_token].lockAmt += pendingAmount;
        IDataStore(datastore).updateData(
            6,
            msg.sender,
            getUserTotalClaimed(msg.sender),
            getPoolTotalAllocatedReward()
        );
    }
    function getAllInvestors() public view returns (address[] memory) {
        return investorsArray;
    }
    function getAllEarners() public view returns (address[] memory) {
        return earnersArray;
    }
    function getAllTraders() public view returns (address[] memory) {
        return tradersArray;
    }
    function getAllReferrers() public view returns (address[] memory) {
        return referrersArray;
    }

    function _deposit(
        address _token,
        uint256 _amount,
        address _referrer,
        uint8 _type
    ) private {
        require(block.timestamp >= startDate, "Can't deposit at this moment");
        require(isListToken(_token), "This is not listed token");
        require(
            poolInfo[tokenPid[_token]].stakeAmt + _amount <=
                poolInfo[tokenPid[_token]].totalStakeLimit,
            "Overflow Total Deposit Limit"
        );
        userInfo[msg.sender][_token].token = _token;
        if (!invested[msg.sender]) {
            invested[msg.sender] = true;
            investorsArray.push(msg.sender);
        }

        if (_type == 0) {
            // stake
            if (!isEarner[msg.sender]) {
                isEarner[msg.sender] = true;
                earnersArray.push(msg.sender);
            }
            claimUpdate(msg.sender, _token);
            uint256 feeAmount = (_amount * depositFee) / percentRate;
            userInfo[msg.sender][_token].lockAmt += _amount;
            poolInfo[tokenPid[_token]].stakeAmt += _amount;
            IERC20(_token).safeTransfer(treasury, feeAmount);
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalLock(msg.sender),
                getPoolTotalLock()
            );
            IDataStore(datastore).updatePoolData(
                _token,
                poolInfo[tokenPid[_token]].stakeAmt,
                poolInfo[tokenPid[_token]].claimed
            );
        } else if (_type == 1) {
            // trade
            if (!isTrader[msg.sender]) {
                isTrader[msg.sender] = true;
                tradersArray.push(msg.sender);
            }
            userInfo[msg.sender][_token].tradeCollateralAmt += _amount;
            poolInfo[tokenPid[_token]].tradeCollateralAmt += _amount;
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalTradeCollateral(msg.sender),
                getPoolTotalTradeCollateral()
            );
        } else if (_type == 2) {
            // borrow
            userInfo[msg.sender][_token].borrowCollateralAmt += _amount;
            poolInfo[tokenPid[_token]].borrowCollateralAmt += _amount;
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalBorrowCollateral(msg.sender),
                getPoolTotalBorrowCollateral()
            );
        }
        if (
            referralInfo[msg.sender].referrer == address(0) &&
            _referrer != msg.sender &&
            _referrer != address(0)
        ) {
            referralInfo[msg.sender].referrer = _referrer;
            if (referralInfo[_referrer].count == 0) {
                referrersArray.push(_referrer);
            }
            referralInfo[_referrer].count += 1;
        }
        if (referralInfo[msg.sender].referrer != address(0)) {
            _referrer = referralInfo[msg.sender].referrer;
            uint256 _referralFee = referralFee[_referrer];
            if (_referralFee == 0) {
                _referralFee = defaultReferralFee;
            }
            referralInfo[_referrer].amountUSD += getAssetInUSD(_token, _amount);
            referralInfo[_referrer].feeUSD += getAssetInUSD(
                _token,
                (_amount * _referralFee) / percentRate
            );
            IERC20(_token).safeTransfer(
                _referrer,
                (_amount * _referralFee) / percentRate
            );
        }
        _depositToVault(_token);
    }
    function _depositToVault(address _token) internal {
        uint256 _amount = getBalance(_token);
        IERC20(_token).approve(vault[_token], _amount);
        IVault(vault[_token]).deposit(_token, _amount);
    }
    function depositToVault(address _token) external onlyTradeBorrow {
        _depositToVault(_token);
    }
    function updateReferralInfo(
        address _referrer,
        uint256 sumAmt,
        uint256 feeAmt
    ) public onlyTrade {
        referralInfo[_referrer].amountUSD += sumAmt;
        referralInfo[_referrer].feeUSD += feeAmt;
    }

    function zapDepositETH(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address _zapOutToken,
        address _referrer,
        uint8 _type
    ) public payable nonReentrant {
        require(msg.value > 0, "No ETH sent");
        IWETH(weth).deposit{value: msg.value}();
        uint _zapOutAmount = msg.value;
        if(_zapOutToken != weth){
            address swapRouter = ITrade(trade).swapProxyArray(swapProxy_index);
            IERC20(weth).approve(swapRouter, msg.value);
            (bool success, bytes memory returnData) = swapRouter.call{value: 0}(swapDataParam);
            require(success, "swap-failed");
            _zapOutAmount = abi.decode(returnData, (uint256));
        }
        _deposit(_zapOutToken, _zapOutAmount, _referrer, _type);
    }
    function zapDeposit(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address _zapInToken,
        uint256 _zapInAmount,
        address _zapOutToken,
        address _referrer,
        uint8 _type
    ) public nonReentrant{
        IERC20(_zapInToken).safeTransferFrom(msg.sender, address(this), _zapInAmount);
        uint _zapOutAmount = _zapInAmount;
        if(_zapInToken !=  _zapOutToken){
            address swapRouter = ITrade(trade).swapProxyArray(swapProxy_index);
            IERC20(_zapInToken).approve(swapRouter, _zapInAmount);
            (bool success, bytes memory returnData) = swapRouter.call{value: 0}(swapDataParam);
            require(success, "swap-failed");
            _zapOutAmount = abi.decode(returnData, (uint256));
        }
        _deposit(_zapOutToken, _zapOutAmount, _referrer, _type);
    }
    
    function unlock(
        address _token,
        uint256 _amount,
        uint8 _type
    ) public nonReentrant {
        require(isListToken(_token), "This is not listed token");
        if (_type == 0) {
            claimUpdate(msg.sender, _token);
            uint256 lockAmt = userInfo[msg.sender][_token].lockAmt;
            if (_amount == MAX_256) {
                _amount = lockAmt;
            }
            require(lockAmt >= _amount, "balance over");
            require(
                poolInfo[tokenPid[_token]].stakeAmt >= _amount,
                "pool balance less"
            );

            userInfo[msg.sender][_token].lockAmt -= _amount;
            poolInfo[tokenPid[_token]].stakeAmt -= _amount;
            userInfo[msg.sender][_token].reqWithdrawAmt += _amount;
            userInfo[msg.sender][_token].unlockTime = block.timestamp;
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalLock(msg.sender),
                getPoolTotalLock()
            );
            IDataStore(datastore).updatePoolData(
                _token,
                poolInfo[tokenPid[_token]].stakeAmt,
                poolInfo[tokenPid[_token]].claimed
            );
        } else if (_type == 1) {
            uint256 _removableAmt = ITrade(trade).getCheckRemovableAmt(
                msg.sender,
                _token
            );
            if (_amount == MAX_256) {
                _amount = _removableAmt;
            }
            require(
                _removableAmt >= _amount &&
                    userInfo[msg.sender][_token].tradeCollateralAmt >= _amount,
                "balance over"
            );
            require(
                poolInfo[tokenPid[_token]].tradeCollateralAmt >= _amount,
                "pool balance less"
            );

            userInfo[msg.sender][_token].tradeCollateralAmt -= _amount;
            poolInfo[tokenPid[_token]].tradeCollateralAmt -= _amount;
            userInfo[msg.sender][_token].reqWithdrawAmt += _amount;
            userInfo[msg.sender][_token].unlockTime = block.timestamp;
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalTradeCollateral(msg.sender),
                getPoolTotalTradeCollateral()
            );
        } else if (_type == 2) {
            uint256 _removableAmt = IBorrow(borrow).getCollateralRemovableAmt(
                msg.sender,
                _token
            );
            if (_amount == MAX_256) {
                _amount = _removableAmt;
            }
            require(
                _removableAmt >= _amount &&
                    userInfo[msg.sender][_token].borrowCollateralAmt >= _amount,
                "balance over"
            );
            require(
                poolInfo[tokenPid[_token]].borrowCollateralAmt >= _amount,
                "pool balance less"
            );

            userInfo[msg.sender][_token].borrowCollateralAmt -= _amount;
            poolInfo[tokenPid[_token]].borrowCollateralAmt -= _amount;
            userInfo[msg.sender][_token].reqWithdrawAmt += _amount;
            userInfo[msg.sender][_token].unlockTime = block.timestamp;
            IDataStore(datastore).updateData(
                _type,
                msg.sender,
                getUserTotalBorrowCollateral(msg.sender),
                getPoolTotalBorrowCollateral()
            );
        }
    }

    function withdraw(
        bytes memory swapDataParam,
        uint256 swapProxy_index,
        address _zapInToken,
        address _zapOutToken
    ) public nonReentrant {
        require(
            block.timestamp >
                userInfo[msg.sender][_zapInToken].unlockTime + LOCK_PERIOD
        ); // unlock period is 5 min
        uint256 withdrawAmt = userInfo[msg.sender][_zapInToken].reqWithdrawAmt;
        require(withdrawAmt > 0, "You can't withdraw 0 balance");
        uint256 _bal = IVault(vault[_zapInToken]).getBalance(_zapInToken);
        if (_bal >= withdrawAmt) {
            userInfo[msg.sender][_zapInToken].reqWithdrawAmt = 0;
        } else {
            userInfo[msg.sender][_zapInToken].reqWithdrawAmt -= _bal;
            withdrawAmt = _bal;
        }
        IVault(vault[_zapInToken]).withdraw(_zapInToken, withdrawAmt);
        if(_zapInToken == _zapOutToken){
            if (_zapInToken == weth) {
                IWETH(weth).withdraw(withdrawAmt);
                payable(msg.sender).transfer(withdrawAmt);
            } else {
                IERC20(_zapInToken).safeTransfer(msg.sender, withdrawAmt);
            }
        }
        else{
            address swapRouter = ITrade(trade).swapProxyArray(swapProxy_index);
            IERC20(_zapInToken).approve(swapRouter, withdrawAmt);
            (bool success, bytes memory returnData) = swapRouter.call{value: 0}(swapDataParam);
            require(success, "swap-failed");
            uint256 _zapOutAmount = abi.decode(returnData, (uint256));
            if (_zapOutToken == weth) {
                IWETH(weth).withdraw(_zapOutAmount);
                payable(msg.sender).transfer(_zapOutAmount);
            } else {
                IERC20(_zapOutToken).safeTransfer(msg.sender, _zapOutAmount);
            }
        }

    }

    // ######### view functions
    function checkPoolDuplicate(address _token) internal view {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            require(
                poolInfo[pid].token != _token,
                "StakingPool: existing pool?"
            );
        }
    }

    function isListToken(address _token) public view returns (bool status) {
        status = false;
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            if (poolInfo[_pid].token == _token) {
                status = true;
            }
        }
    }
    function getBalance(address _token) internal view returns (uint256) {
        return IERC20(_token).balanceOf(address(this));
    }

    function getUserWalletBalance(
        address _user
    ) public view returns (WalletInfo[] memory) {
        WalletInfo[] memory _info = new WalletInfo[](poolInfo.length);
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            address _token = poolInfo[_pid].token;
            uint8 _decimals = IERC20(_token).decimals();
            uint256 _amount = IERC20(_token).balanceOf(_user);
            if (_token == weth) {
                _amount = _user.balance;
            }
            _info[_pid] = WalletInfo({
                token: _token,
                decimals: _decimals,
                amount: _amount
            });
        }
        return _info;
    }
    function getTotalValueLocked(
        address _token
    ) public view returns (uint256 _amount) {
        _amount =
            poolInfo[tokenPid[_token]].stakeAmt +
            poolInfo[tokenPid[_token]].tradeCollateralAmt +
            poolInfo[tokenPid[_token]].borrowCollateralAmt;
    }
    function getTotalValueUsing(
        address _token
    ) public view returns (uint256 _amount) {
        _amount =
            poolInfo[tokenPid[_token]].tradeUsingAmt +
            poolInfo[tokenPid[_token]].borrowUsingAmt;
    }

    function getAssetInUSD(
        address _token,
        uint256 _amount
    ) internal view returns (uint256) {
        return
            (IPriceOracle(priceoracle).getPrice(_token) * _amount) /
            (10 ** IERC20(_token).decimals());
    }
    function getUSDInAsset(
        address _token,
        uint256 _amtUSD
    ) internal view returns (uint256) {
        return
            (_amtUSD * (10 ** IERC20(_token).decimals())) /
            IPriceOracle(priceoracle).getPrice(_token);
    }
    // external view functions
    function getPoolInfo() external view returns (PoolInfo[] memory) {
        return poolInfo;
    }

    function getUserInfo(
        address _user
    ) external view returns (UserInfo[] memory) {
        UserInfo[] memory _info = new UserInfo[](poolInfo.length);
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            address _token = poolInfo[_pid].token;
            uint256 _lockAmt = userInfo[_user][_token].lockAmt;
            uint256 _reqWithdrawAmt = userInfo[_user][_token].reqWithdrawAmt;
            uint256 _tradeCollateralAmt = userInfo[_user][_token]
                .tradeCollateralAmt;
            uint256 _borrowCollateralAmt = userInfo[_user][_token]
                .borrowCollateralAmt;
            uint256 _unlockTime = userInfo[_user][_token].unlockTime;
            uint256 _claimedAmt = userInfo[_user][_token].claimedAmt;
            uint256 _lastClaimTime = userInfo[_user][_token].lastClaimTime;
            uint256 _apr = poolInfo[tokenPid[_token]].apr;

            uint256 lastRoiTime = block.timestamp - _lastClaimTime;
            uint256 pendingAmount = (lastRoiTime * _lockAmt * _apr) /
                percentRate /
                rewardPeriod;

            _info[_pid] = UserInfo({
                token: _token,
                lockAmt: _lockAmt + pendingAmount,
                lockUSD: getAssetInUSD(_token, _lockAmt + pendingAmount),
                reqWithdrawAmt: _reqWithdrawAmt,
                reqWithdrawUSD: getAssetInUSD(_token, _reqWithdrawAmt),
                tradeCollateralAmt: _tradeCollateralAmt,
                tradeCollateralUSD: getAssetInUSD(_token, _tradeCollateralAmt),
                borrowCollateralAmt: _borrowCollateralAmt,
                borrowCollateralUSD: getAssetInUSD(
                    _token,
                    _borrowCollateralAmt
                ),
                unlockTime: _unlockTime,
                claimedAmt: _claimedAmt + pendingAmount,
                claimedUSD: getAssetInUSD(_token, _claimedAmt + pendingAmount),
                lastClaimTime: _lastClaimTime
            });
        }
        return _info;
    }
    function getTotalValueUsable(
        address _token
    ) public view returns (uint256 _amount) {
        _amount = 0;
        if (getTotalValueLocked(_token) > getTotalValueUsing(_token)) {
            _amount = getTotalValueLocked(_token) - getTotalValueUsing(_token);
        }
    }
    function getTotalValueUsableList()
        external
        view
        returns (WalletInfo[] memory)
    {
        WalletInfo[] memory _info = new WalletInfo[](poolInfo.length);
        for (uint256 _pid = 0; _pid < poolInfo.length; _pid++) {
            address _token = poolInfo[_pid].token;
            uint8 _decimals = IERC20(_token).decimals();
            uint256 _amount = getTotalValueUsable(_token);
            _info[_pid] = WalletInfo({
                token: _token,
                decimals: _decimals,
                amount: _amount
            });
        }
        return _info;
    }
    function getPidByToken(
        address _token
    ) external view returns (uint256 _pid) {
        _pid = tokenPid[_token];
    }

    function wrapETH() internal {
        require(msg.value > 0, "No ETH sent");

        // Deposit ETH to WETH contract to wrap it
        IWETH(weth).deposit{value: msg.value}();

        emit Wrapped(msg.sender, msg.value);
    }

    receive() external payable {
        assert(msg.sender == weth); // only accept ETH via fallback from the WETH contract
    }
}
