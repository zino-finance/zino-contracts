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

    function decimals() external view returns (uint8);

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

// import "@openzeppelin/contracts/token/ERC20/IERC20Metadata.sol";

struct PoolInfo {
    address token;
    uint256 apr;
    uint256 stakeAmt;
    uint256 totalStakeLimit;
}
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

interface IStaking {
    function transferToZino(address token, uint256 tokenAmount) external;
    function updateBorrowUsingAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external;
    function updateLockAmt(
        address _token,
        uint256 _amount,
        bool _increase
    ) external;
    function borrowCollateralToBorrowedFunds(address _user) external;
    function getPoolInfo() external view returns (PoolInfo[] memory);
    function getUserInfo(
        address _user
    ) external view returns (UserInfo[] memory);
    function getTotalValueUsable(
        address _token
    ) external view returns (uint256 _amount);
    function getPidByToken(address _token) external view returns (uint256 _pid);
    function depositToVault(address _token) external;
    function liquidate(address _user, bool _type) external;
    function increasePoolSrcDstAmt(address _token, uint256 _amount, bool _type) external;
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
    function updateBorrowAPR(
        address[] calldata _tokens,
        uint256[] calldata _aprs
    ) external;
}
contract Borrow is ReentrancyGuard {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;
    // governance
    address public operator;
    uint256 public borrow_id = 0;
    address public staking;
    address public executor;
    address public datastore;
    // Info of each user.
    struct BorrowInfo {
        address token;
        uint256 amount;
        uint256 amountUSD;
        uint256 lastBorrowTime;
    }
    struct BorrowableInfo {
        address token;
        uint256 amount;
        uint256 amountUSD;
    }
    struct BorrowAssets {
        address token;
        uint256 apr;
        uint256 totalBorrowAmt;
        uint256 totalBorrowLimit;
    }
    struct LiquidateInfo {
        address token;
        uint256 amount;
    }

    BorrowAssets[] public borrowAssets;
    address[] public borrowers;
    mapping(address => mapping(address => BorrowInfo)) public borrowInfo;
    mapping(address => address) public altexecutor;
    uint256 public borrowRate = 7500; // 75%    $100 collateral => $75 borrowable
    uint256 public liquidateRate = 9000; // 90%
    uint256 public percentRate = 10000;
    uint8 public USDDECIMAL = 8;
    address public priceoracle = 0x2bE2f60Df305E4Ec5cDB88EEDD686c4CE473Fd52;
    uint256 public rewardPeriod = 1 days;
    mapping(address => uint256) public tokenPid;
    address public constant weth = 0x82aF49447D8a07e3bd95BD0d56f35241523fBab1;

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(
        address indexed user,
        uint256 indexed pid,
        uint256 amount
    );
    event RewardPaid(address indexed user, uint256 amount);
    event Wrapped(address sender, uint amount);

    constructor(address _staking) {
        operator = msg.sender;
        staking = _staking;
        executor = msg.sender;

        addBorrowAssets(0x82aF49447D8a07e3bd95BD0d56f35241523fBab1, 290, 1e22); // WETH
        addBorrowAssets(0xFd086bC7CD5C481DCC9C85ebE478A1C0b69FCbb9, 1125, 1e12); // USDT
        addBorrowAssets(0xaf88d065e77c8cC2239327C5EDb3A432268e5831, 1056, 1e12); // USDC
        addBorrowAssets(0x2f2a2543B76A4166549F7aaB2e75Bef0aefC5B0f, 25, 1e10); // WBTC
        addBorrowAssets(0xFF970A61A04b1cA14834A43f5dE4533eBDDB5CC8, 2026, 1e12); // USDC.e
        addBorrowAssets(0xFa7F8980b0f1E64A2062791cc3b0871572f1F7f0, 1526, 1e25); // UNI
        addBorrowAssets(0x0c880f6761F1af8d9Aa9C466984b80DAb9a8c9e8, 1256, 1e25); // Pendle
        addBorrowAssets(0x912CE59144191C1204E64559FE8253a0e49E6548, 152, 1e25); // ARB
        addBorrowAssets(0xf97f4df75117a78c1A5a0DBb814Af92458539FB4, 79, 1e25); // LINK
        addBorrowAssets(0x5979D7b546E38E414F7E9822514be443A4800529, 30, 1e22); // wstETH
        addBorrowAssets(0xEC70Dcb4A1EFa46b8F2D97C310C9c4790ba5ffA8, 45, 1e22); // rETH
        addBorrowAssets(0x35751007a407ca6FEFfE80b3cB397736D2cf4dbe, 154, 1e22); // weETH
        addBorrowAssets(0x2416092f143378750bb29b79eD961ab195CcEea5, 75, 1e22); // ezETH
        addBorrowAssets(0xfc5A1A6EB076a2C7aD06eD22C90d7E710E35ad0a, 789, 1e22); // GMX
    }
    modifier onlyOperator() {
        require(operator == msg.sender, "borrow: caller is not the operator");
        _;
    }
    modifier onlyExecutor() {
        require(executor == msg.sender, "borrow: caller is not the executor");
        _;
    }
    function setDataStore(address _datastore) public onlyOperator {
        datastore = _datastore;
    }
    function setExecutor(address _executor) public onlyOperator {
        executor = _executor;
    }
    function setOperator(address _operator) public onlyOperator {
        operator = _operator;
    }

    function addBorrowAssets(
        address _token,
        uint256 _apr,
        uint256 _totalBorrowLimit
    ) public onlyOperator {
        checkPoolDuplicate(_token);
        uint256 _pid = borrowAssets.length;
        tokenPid[_token] = _pid;
        borrowAssets.push(
            BorrowAssets({
                token: _token,
                apr: _apr,
                totalBorrowAmt: 0,
                totalBorrowLimit: _totalBorrowLimit
            })
        );
    }

    function updateBorrowAssets(
        address _token,
        uint256 _apr,
        uint256 _totalBorrowLimit
    ) public onlyOperator {
        require(isBorrowToken(_token), "Not listed token");
        uint256 _pid = tokenPid[_token];
        borrowAssets[_pid].apr = _apr;
        borrowAssets[_pid].totalBorrowLimit = _totalBorrowLimit;
    }

    function setBorrowAPR(
        address[] calldata _tokens,
        uint256[] calldata _aprs
    ) public onlyExecutor {
        require(_tokens.length == _aprs.length, "Invalid input length");
        for (uint256 i = 0; i < _tokens.length; i++) {
            require(isBorrowToken(_tokens[i]), "Not listed token");
            uint256 _pid = tokenPid[_tokens[i]];
            borrowAssets[_pid].apr = _aprs[i];
        }
        IDataStore(datastore).updateBorrowAPR(_tokens, _aprs);
    }

    function setstaking(address _staking) public onlyOperator {
        staking = _staking;
    }

    // user functions
    function updateAltExecutor(bool _set) public {
        if (_set) {
            altexecutor[msg.sender] = executor;
        } else {
            altexecutor[msg.sender] = msg.sender;
        }
    }

    function feeUpdate(address _user, address _btoken) private {
        uint256 feeAmount = getFeeAmount(_user, _btoken);
        IStaking(staking).updateLockAmt(_btoken, feeAmount, true);
        IStaking(staking).updateBorrowUsingAmt(_btoken, feeAmount, true);
        borrowInfo[_user][_btoken].amount += feeAmount;
        borrowInfo[_user][_btoken].lastBorrowTime = block.timestamp;
    }
    function borrow(
        address user,
        address _btoken,
        uint256 _bamt
    ) public nonReentrant {
        require(
            msg.sender == user || msg.sender == altexecutor[user],
            "caller has no permission"
        );
        require(
            IStaking(staking).getTotalValueUsable(_btoken) >= _bamt,
            "Total Usable Balance overflow"
        );
        require(_bamt > 0, "You can't borrow ZERO amount");
        // check the collateral funds are enough to borrow
        require(isBorrowToken(_btoken), "It is not a borrow token");

        uint256 _borrowableAmt = getBorrowableAmt(user, _btoken);

        require(_bamt <= _borrowableAmt, "overflow borrow limit");

        // update borrow amount considering the borrow fee
        feeUpdate(user, _btoken);
        // borrow
        borrowInfo[user][_btoken].token = _btoken;
        borrowInfo[user][_btoken].amount += _bamt;
        borrowInfo[user][_btoken].lastBorrowTime = block.timestamp;
        IStaking(staking).transferToZino(_btoken, _bamt);
        IStaking(staking).updateBorrowUsingAmt(_btoken, _bamt, true);

        if (_btoken == weth) {
            IWETH(weth).withdraw(_bamt);
            payable(user).transfer(_bamt);
        } else {
            IERC20(_btoken).safeTransfer(user, _bamt);
        }
        addBorrower(user);

        IDataStore(datastore).updateData(8, user, getBorrowsInUSD(user), 0);
    }
    function getAllBorrowers() public view returns (address[] memory) {
        return borrowers;
    }
    function addBorrower(address _user) internal {
        bool _repeat_status = false;
        for (uint256 _index = 0; _index < borrowers.length; _index++) {
            if (borrowers[_index] == _user) {
                _repeat_status = true;
            }
        }
        if (!_repeat_status) {
            borrowers.push(_user);
        }
    }
    function removeBorrower(address _user) internal {
        uint256 _index;
        for (_index = 0; _index < borrowers.length; _index++) {
            if (borrowers[_index] == _user) {
                break;
            }
        }
        for (uint i = _index; i < borrowers.length - 1; i++) {
            borrowers[i] = borrowers[i + 1];
        }
        borrowers.pop();
    }

    function repay(
        address user,
        address _btoken,
        uint256 _bamt
    ) public nonReentrant {
        require(
            msg.sender == user || msg.sender == altexecutor[user],
            "caller has no permission"
        );
        require(_btoken != weth, "Call repayETH function");
        require(isBorrowToken(_btoken), "It is not a borrow token");
        feeUpdate(user, _btoken);
        if (borrowInfo[user][_btoken].amount < _bamt) {
            _bamt = borrowInfo[user][_btoken].amount;
        }

        // repay
        IERC20(_btoken).safeTransferFrom(user, staking, _bamt);
        IStaking(staking).depositToVault(_btoken);
        borrowInfo[user][_btoken].token = _btoken;
        borrowInfo[user][_btoken].amount -= _bamt;
        IStaking(staking).updateBorrowUsingAmt(_btoken, _bamt, false);

        // if(borrowInfo[user][_btoken].amount==0){
        //     removeBorrower(user);
        // }
    }
    function repayETH(address user) public payable nonReentrant {
        require(
            msg.sender == user || msg.sender == altexecutor[user],
            "caller has no permission"
        );
        address _btoken = weth;
        uint256 _bamt = msg.value;
        feeUpdate(user, _btoken);
        if (borrowInfo[user][_btoken].amount < _bamt) {
            _bamt = borrowInfo[user][_btoken].amount;
        }

        // repay
        borrowInfo[user][_btoken].token = _btoken;
        borrowInfo[user][_btoken].amount -= _bamt;
        IStaking(staking).updateBorrowUsingAmt(_btoken, _bamt, false);
    }
    function getLiquidateUsers() public view returns(address[] memory){
        uint256 len = 0;
        for(uint256 i = 0 ; i < borrowers.length ; i++){
            if(liquidateNeeded(borrowers[i])){
                len++;
            }
        }
        address[] memory _liquidateUsers = new address[](len);
        uint256 index = 0;
        for(uint256 i = 0 ; i < borrowers.length ; i++){
            if(liquidateNeeded(borrowers[i])){
                _liquidateUsers[index++] = borrowers[i];
            }
        }
        return _liquidateUsers;
    }
    function liquidateAll() public {
        for (uint256 i = 0; i < borrowers.length; i++) {
            address _user = borrowers[i];
            if (liquidateNeeded(_user)) {
                liquidate(_user);
            }
        }
    }
    function liquidate(address _user) public {
        require(
            (getCollateralsInUSD(_user) * liquidateRate) / percentRate <=
                getBorrowsInUSD(_user),
            "Not eligible to liquidate"
        );

        BorrowInfo[] memory _borrowInfo = getBorrowInfo(_user);
        for (uint256 i = 0; i < _borrowInfo.length; i++) {
            address _btoken = _borrowInfo[i].token;
            IStaking(staking).updateLockAmt(_btoken, getFeeAmount(_user, _btoken), true); // increase lock amount 
            IStaking(staking).increasePoolSrcDstAmt(_btoken, _borrowInfo[i].amount, false); // increase PoolDstAmt 
            borrowInfo[_user][_btoken].amount = 0;
            IStaking(staking).updateBorrowUsingAmt(_btoken, borrowInfo[_user][_btoken].amount, false);
        }
        IStaking(staking).liquidate(_user, false);
        
    }

    // internal view functions
    function checkPoolDuplicate(address _token) internal view {
        uint256 length = borrowAssets.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            require(
                borrowAssets[pid].token != _token,
                "StakingPool: existing pool?"
            );
        }
    }

    // public view functions
    function isBorrowToken(address _token) public view returns (bool status) {
        status = false;
        for (uint256 _pid = 0; _pid < borrowAssets.length; _pid++) {
            if (borrowAssets[_pid].token == _token) {
                status = true;
            }
        }
    }
    function getAssetInUSD(
        address _token,
        uint256 _amount
    ) public view returns (uint256) {
        return
            (IPriceOracle(priceoracle).getPrice(_token) * _amount) /
            (10 ** IERC20(_token).decimals());
    }
    function getBorrowsInUSD(address _user) public view returns (uint256) {
        uint256 _amtUSD = 0;
        BorrowInfo[] memory _borrowInfo = getBorrowInfo(_user);
        for (uint256 i = 0; i < _borrowInfo.length; i++) {
            _amtUSD += getAssetInUSD(
                _borrowInfo[i].token,
                _borrowInfo[i].amount
            );
        }
        return _amtUSD;
    }
    function getFeeAmount(
        address _user,
        address _btoken
    ) public view returns (uint256 feeAmount) {
        uint256 lastborrowPeriod = block.timestamp -
            borrowInfo[_user][_btoken].lastBorrowTime;
        feeAmount =
            (lastborrowPeriod *
                borrowInfo[_user][_btoken].amount *
                borrowAssets[tokenPid[_btoken]].apr) /
            percentRate /
            rewardPeriod;
    }
    function getUSDInAsset(
        address _token,
        uint256 _amtUSD
    ) public view returns (uint256) {
        return
            (_amtUSD * (10 ** IERC20(_token).decimals())) /
            IPriceOracle(priceoracle).getPrice(_token);
    }
    function getBorrowableAmt(
        address _user,
        address _btoken
    ) public view returns (uint256 _bamt) {
        uint256 _bamtUSD;
        if (
            (getCollateralsInUSD(_user) * borrowRate) / percentRate <
            getBorrowsInUSD(_user)
        ) {
            _bamtUSD = 0;
        } else {
            _bamtUSD =
                (getCollateralsInUSD(_user) * borrowRate) /
                percentRate -
                getBorrowsInUSD(_user);
        }
        _bamt = getUSDInAsset(_btoken, _bamtUSD);
    }
    function getCollateralRemovableAmt(
        address _user,
        address _ctoken
    ) public view returns (uint256) {
        uint256 _camt = 0;
        uint256 _camtUSD;
        uint256 _pid;
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        if (
            getCollateralsInUSD(_user) <=
            (getBorrowsInUSD(_user) / borrowRate) * percentRate
        ) {
            return _camt;
        } else {
            _camtUSD =
                getCollateralsInUSD(_user) -
                (getBorrowsInUSD(_user) / borrowRate) *
                percentRate;
        }
        _camt = getUSDInAsset(_ctoken, _camtUSD);

        _pid = IStaking(staking).getPidByToken(_ctoken);
        if (_userInfo[_pid].borrowCollateralAmt < _camt) {
            _camt = _userInfo[_pid].borrowCollateralAmt;
        }
        return _camt;
    }
    function getCollateralRemoveAmtList(
        address _user
    ) public view returns (BorrowInfo[] memory) {
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        BorrowInfo[] memory _borrowInfo = new BorrowInfo[](_userInfo.length);
        for (uint256 i = 0; i < _userInfo.length; i++) {
            address _token = borrowAssets[i].token;
            uint256 _amount = getCollateralRemovableAmt(_user, _token);
            _borrowInfo[i] = BorrowInfo({
                token: _token,
                amount: _amount,
                amountUSD: 0,
                lastBorrowTime: 0
            });
        }
        return _borrowInfo;
    }
    function getCollateralsInUSD(address _user) public view returns (uint256) {
        uint256 _amtUSD = 0;
        UserInfo[] memory _userInfo = IStaking(staking).getUserInfo(_user);
        for (uint256 i = 0; i < _userInfo.length; i++) {
            _amtUSD += getAssetInUSD(
                _userInfo[i].token,
                _userInfo[i].borrowCollateralAmt
            );
        }
        return _amtUSD;
    }
    function getBorrowInfo(
        address _user
    ) public view returns (BorrowInfo[] memory) {
        BorrowInfo[] memory _borrowInfo = new BorrowInfo[](borrowAssets.length);
        for (uint256 i = 0; i < borrowAssets.length; i++) {
            address _token = borrowAssets[i].token;
            uint256 _amount = borrowInfo[_user][_token].amount +
                getFeeAmount(_user, _token);
            uint256 _amountUSD = getAssetInUSD(_token, _amount);
            _borrowInfo[i] = BorrowInfo({
                token: _token,
                amount: _amount,
                amountUSD: _amountUSD,
                lastBorrowTime: borrowInfo[_user][_token].lastBorrowTime
            });
        }
        return _borrowInfo;
    }
    function getBorrowableInfo(
        address _user
    ) public view returns (BorrowableInfo[] memory) {
        BorrowableInfo[] memory _borrowableInfo = new BorrowableInfo[](
            borrowAssets.length
        );
        for (uint256 i = 0; i < borrowAssets.length; i++) {
            address _token = borrowAssets[i].token;
            uint256 _amount = getBorrowableAmt(_user, _token);
            uint256 _borrowableUSD = getAssetInUSD(_token, _amount);
            _borrowableInfo[i] = BorrowableInfo({
                token: _token,
                amount: _amount,
                amountUSD: _borrowableUSD
            });
        }
        return _borrowableInfo;
    }

    function liquidateNeeded(
        address _user
    ) public view returns (bool isNeeded) {
        return
            (getCollateralsInUSD(_user) * liquidateRate) / percentRate <
            getBorrowsInUSD(_user);
    }
    function getAssetsInfo() external view returns (BorrowAssets[] memory) {
        return borrowAssets;
    }

    function wrapETH() internal {
        require(msg.value > 0, "No ETH sent");

        // Deposit ETH to WETH contract to wrap it
        IWETH(weth).deposit{value: msg.value}();
        IERC20(weth).safeTransfer(staking, msg.value);

        emit Wrapped(msg.sender, msg.value);
    }
    receive() external payable {
        // Wrap the received ETH into WETH
        wrapETH();
    }
}
