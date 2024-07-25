// SPDX-License-Identifier: SimPL-2.0
pragma solidity ^0.6.0;
pragma experimental ABIEncoderV2;

/**
 * @title Ownable
 * @dev The Ownable contract has an owner address, and provides basic authorization control
 * functions, this simplifies the implementation of "user permissions".
 */
contract Ownable {
    address private _owner;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev The Ownable constructor sets the original `owner` of the contract to the sender
     * account.
     */
    constructor () internal {
        _owner = msg.sender;
        emit OwnershipTransferred(address(0), _owner);
    }

    /**
     * @return the address of the owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(isOwner(), 'Ownable: caller is not the owner');
        _;
    }

    /**
     * @return true if `msg.sender` is the owner of the contract.
     */
    function isOwner() public view returns (bool) {
        return msg.sender == _owner;
    }

    /**
     * @dev Allows the current owner to relinquish control of the contract.
     * It will not be possible to call the functions with the `onlyOwner`
     * modifier anymore.
     * @notice Renouncing ownership will leave the contract without an owner,
     * thereby removing any functionality that is only available to the owner.
     */
    function renounceOwnership() public onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Allows the current owner to transfer control of the contract to a newOwner.
     * @param newOwner The address to transfer ownership to.
     */
    function transferOwnership(address newOwner) public onlyOwner {
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers control of the contract to a newOwner.
     * @param newOwner The address to transfer ownership to.
     */
    function _transferOwnership(address newOwner) internal {
        require(newOwner != address(0),'Ownable: _transferOwnership can not transfer ownership to zero address');
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    function initOwner(address addr) public {
        require(_owner == address(0),'initOwner can only run once');

        _transferOwnership(addr);
    }
}

interface IERC20 {
    function transfer(address to, uint256 value) external returns (bool);

    function approve(address spender, uint256 value) external returns (bool);

    function transferFrom(address from, address to, uint256 value) external returns (bool);

    function totalSupply() external view returns (uint256);

    function balanceOf(address who) external view returns (uint256);

    function allowance(address owner, address spender) external view returns (uint256);

    event Transfer(address indexed from, address indexed to, uint256 value);

    event Approval(address indexed owner, address indexed spender, uint256 value);

    //mint and burn
    function decimals() external view returns (uint8);
    function mint(address to, uint256 value) external;
    function burn(address to, uint256 value) external;
}

interface IERC721 {

  event Transfer(address indexed from, address indexed to, uint256 indexed tokenId);
  event Approval(address indexed owner,address indexed approved,uint256 indexed tokenId);
  event ApprovalForAll(address indexed owner,address indexed operator,bool approved);

  function balanceOf(address owner) external view returns (uint256 balance);
  function ownerOf(uint256 tokenId) external view returns (address owner);

  function approve(address to, uint256 tokenId) external;
  function getApproved(uint256 tokenId) external view returns (address operator);

  function setApprovalForAll(address operator, bool _approved) external;
  function isApprovedForAll(address owner, address operator) external view returns (bool);

  function transferFrom(address from, address to, uint256 tokenId) external;
  function safeTransferFrom(address from, address to, uint256 tokenId) external;

  function safeTransferFrom(address from,address to, uint256 tokenId, bytes calldata data) external;

  //mint
  function mint(address addr,uint256 nftid) external;
}

interface ERC1155 /* is ERC165 */ {
    /**
        @dev Either `TransferSingle` or `TransferBatch` MUST emit when tokens are transferred, including zero value transfers as well as minting or burning (see "Safe Transfer Rules" section of the standard).
        The `_operator` argument MUST be the address of an account/contract that is approved to make the transfer (SHOULD be msg.sender).
        The `_from` argument MUST be the address of the holder whose balance is decreased.
        The `_to` argument MUST be the address of the recipient whose balance is increased.
        The `_id` argument MUST be the token type being transferred.
        The `_value` argument MUST be the number of tokens the holder balance is decreased by and match what the recipient balance is increased by.
        When minting/creating tokens, the `_from` argument MUST be set to `0x0` (i.e. zero address).
        When burning/destroying tokens, the `_to` argument MUST be set to `0x0` (i.e. zero address).        
    */
    event TransferSingle(address indexed _operator, address indexed _from, address indexed _to, uint256 _id, uint256 _value);

    /**
        @dev Either `TransferSingle` or `TransferBatch` MUST emit when tokens are transferred, including zero value transfers as well as minting or burning (see "Safe Transfer Rules" section of the standard).      
        The `_operator` argument MUST be the address of an account/contract that is approved to make the transfer (SHOULD be msg.sender).
        The `_from` argument MUST be the address of the holder whose balance is decreased.
        The `_to` argument MUST be the address of the recipient whose balance is increased.
        The `_ids` argument MUST be the list of tokens being transferred.
        The `_values` argument MUST be the list of number of tokens (matching the list and order of tokens specified in _ids) the holder balance is decreased by and match what the recipient balance is increased by.
        When minting/creating tokens, the `_from` argument MUST be set to `0x0` (i.e. zero address).
        When burning/destroying tokens, the `_to` argument MUST be set to `0x0` (i.e. zero address).                
    */
    event TransferBatch(address indexed _operator, address indexed _from, address indexed _to, uint256[] _ids, uint256[] _values);

    /**
        @dev MUST emit when approval for a second party/operator address to manage all tokens for an owner address is enabled or disabled (absence of an event assumes disabled).        
    */
    event ApprovalForAll(address indexed _owner, address indexed _operator, bool _approved);

    /**
        @dev MUST emit when the URI is updated for a token ID.
        URIs are defined in RFC 3986.
        The URI MUST point to a JSON file that conforms to the "ERC-1155 Metadata URI JSON Schema".
    */
    event URI(string _value, uint256 indexed _id);

    /**
        @notice Transfers `_value` amount of an `_id` from the `_from` address to the `_to` address specified (with safety call).
        @dev Caller must be approved to manage the tokens being transferred out of the `_from` account (see "Approval" section of the standard).
        MUST revert if `_to` is the zero address.
        MUST revert if balance of holder for token `_id` is lower than the `_value` sent.
        MUST revert on any other error.
        MUST emit the `TransferSingle` event to reflect the balance change (see "Safe Transfer Rules" section of the standard).
        After the above conditions are met, this function MUST check if `_to` is a smart contract (e.g. code size > 0). If so, it MUST call `onERC1155Received` on `_to` and act appropriately (see "Safe Transfer Rules" section of the standard).        
        @param _from    Source address
        @param _to      Target address
        @param _id      ID of the token type
        @param _value   Transfer amount
        @param _data    Additional data with no specified format, MUST be sent unaltered in call to `onERC1155Received` on `_to`
    */
    function safeTransferFrom(address _from, address _to, uint256 _id, uint256 _value, bytes calldata _data) external;

    /**
        @notice Transfers `_values` amount(s) of `_ids` from the `_from` address to the `_to` address specified (with safety call).
        @dev Caller must be approved to manage the tokens being transferred out of the `_from` account (see "Approval" section of the standard).
        MUST revert if `_to` is the zero address.
        MUST revert if length of `_ids` is not the same as length of `_values`.
        MUST revert if any of the balance(s) of the holder(s) for token(s) in `_ids` is lower than the respective amount(s) in `_values` sent to the recipient.
        MUST revert on any other error.        
        MUST emit `TransferSingle` or `TransferBatch` event(s) such that all the balance changes are reflected (see "Safe Transfer Rules" section of the standard).
        Balance changes and events MUST follow the ordering of the arrays (_ids[0]/_values[0] before _ids[1]/_values[1], etc).
        After the above conditions for the transfer(s) in the batch are met, this function MUST check if `_to` is a smart contract (e.g. code size > 0). If so, it MUST call the relevant `ERC1155TokenReceiver` hook(s) on `_to` and act appropriately (see "Safe Transfer Rules" section of the standard).                      
        @param _from    Source address
        @param _to      Target address
        @param _ids     IDs of each token type (order and length must match _values array)
        @param _values  Transfer amounts per token type (order and length must match _ids array)
        @param _data    Additional data with no specified format, MUST be sent unaltered in call to the `ERC1155TokenReceiver` hook(s) on `_to`
    */
    function safeBatchTransferFrom(address _from, address _to, uint256[] calldata _ids, uint256[] calldata _values, bytes calldata _data) external;

    /**
        @notice Get the balance of an account's tokens.
        @param _owner  The address of the token holder
        @param _id     ID of the token
        @return        The _owner's balance of the token type requested
     */
    function balanceOf(address _owner, uint256 _id) external view returns (uint256);

    /**
        @notice Get the balance of multiple account/token pairs
        @param _owners The addresses of the token holders
        @param _ids    ID of the tokens
        @return        The _owner's balance of the token types requested (i.e. balance for each (owner, id) pair)
     */
    function balanceOfBatch(address[] calldata _owners, uint256[] calldata _ids) external view returns (uint256[] memory);

    /**
        @notice Enable or disable approval for a third party ("operator") to manage all of the caller's tokens.
        @dev MUST emit the ApprovalForAll event on success.
        @param _operator  Address to add to the set of authorized operators
        @param _approved  True if the operator is approved, false to revoke approval
    */
    function setApprovalForAll(address _operator, bool _approved) external;

    /**
        @notice Queries the approval status of an operator for a given owner.
        @param _owner     The owner of the tokens
        @param _operator  Address of authorized operator
        @return           True if the operator is approved, false if not
    */
    function isApprovedForAll(address _owner, address _operator) external view returns (bool);
}

library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * This test is non-exhaustive, and there may be false-negatives: during the
     * execution of a contract's constructor, its address will be reported as
     * not containing a contract.
     *
     * > It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies in extcodesize, which returns 0 for contracts in
        // construction, since the code is only stored at the end of the
        // constructor execution.

        uint256 size;
        // solhint-disable-next-line no-inline-assembly
        assembly { size := extcodesize(account) }
        return size > 0;
    }
}

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
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
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b <= a, "SafeMath: subtraction overflow");
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-solidity/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        // Solidity only automatically asserts when dividing by 0
        require(b > 0, "SafeMath: division by zero");
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        require(b != 0, "SafeMath: modulo by zero");
        return a % b;
    }
}

library SafeERC20 {
    using SafeMath for uint256;
    using Address for address;

    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        // solhint-disable-next-line max-line-length
        require((value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).add(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 newAllowance = token.allowance(address(this), spender).sub(value);
        callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves.

        // A Solidity high level call has three parts:
        //  1. The target address is checked to verify it contains contract code
        //  2. The call itself is made, and success asserted
        //  3. The return value is decoded, which in turn checks the size of the returned data.
        // solhint-disable-next-line max-line-length
        require(address(token).isContract(), "SafeERC20: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = address(token).call(data);
        require(success, "SafeERC20: low-level call failed");

        if (returndata.length > 0) { // Return data is optional
            // solhint-disable-next-line max-line-length
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}

// File: zos-lib/contracts/upgradeability/Proxy.sol

/**
 * @title Proxy
 * @dev Implements delegation of calls to other contracts, with proper
 * forwarding of return values and bubbling of failures.
 * It defines a fallback function that delegates all calls to the address
 * returned by the abstract _implementation() internal function.
 */
abstract contract Proxy {
  /**
   * @dev Fallback function.
   * Implemented entirely in `_fallback`.
   */
  //function () payable external {
  //    _fallback();
  //}
  fallback() external payable{
    _fallback();
  }

  receive() payable external virtual{
  
  }

  /**
   * @return The Address of the implementation.
   */
  function _implementation() internal view virtual returns (address);

  /**
   * @dev Delegates execution to an implementation contract.
   * This is a low level function that doesn't return to its internal call site.
   * It will return to the external caller whatever the implementation returns.
   * @param implementation Address to delegate.
   */
  function _delegate(address implementation) internal {
    assembly {
        let ptr := mload(0x00)
      // Copy msg.data. We take full control of memory in this inline assembly
      // block because it will not return to Solidity code. We overwrite the
      // Solidity scratch pad at memory position 0.
      calldatacopy(ptr, 0, calldatasize())

      // Call the implementation.
      // out and outsize are 0 because we don't know the size yet.
      let result := delegatecall(gas(), implementation, ptr, calldatasize(), 0, 0)

      // Copy the returned data.
      returndatacopy(ptr, 0, returndatasize())

      switch result
      // delegatecall returns 0 on error.
      case 0 { revert(ptr, returndatasize()) }
      default { return(ptr, returndatasize()) }
    }
  }

  /**
   * @dev Function that is run as the first thing in the fallback function.
   * Can be redefined in derived contracts to add functionality.
   * Redefinitions must call super._willFallback().
   */
  function _willFallback() internal virtual{
  }

  /**
   * @dev fallback implementation.
   * Extracted to enable manual triggering.
   */
  function _fallback() internal {
    _willFallback();
    _delegate(_implementation());
  }
}

// File: openzeppelin-solidity/contracts/AddressUtils.sol

/**
 * Utility library of inline functions on addresses
 */
library AddressUtils {

  /**
   * Returns whether the target address is a contract
   * @dev This function will return false if invoked during the constructor of a contract,
   * as the code is not actually created until after the constructor finishes.
   * @param addr address to check
   * @return whether the target address is a contract
   */
  function isContract(address addr) internal view returns (bool) {
    uint256 size;
    // XXX Currently there is no better way to check if there is a contract in an address
    // than to check the size of the code at that address.
    // See https://ethereum.stackexchange.com/a/14016/36603
    // for more details about how this works.
    // TODO Check this again before the Serenity release, because all addresses will be
    // contracts then.
    // solium-disable-next-line security/no-inline-assembly
    assembly { size := extcodesize(addr) }
    return size > 0;
  }

}

// File: zos-lib/contracts/upgradeability/UpgradeabilityProxy.sol

/**
 * @title UpgradeabilityProxy
 * @dev This contract implements a proxy that allows to change the
 * implementation address to which it will delegate.
 * Such a change is called an implementation upgrade.
 */
contract UpgradeabilityProxy is Proxy {
  /**
   * @dev Emitted when the implementation is upgraded.
   * @param implementation Address of the new implementation.
   */
  event Upgraded(address implementation);

  /**
   * @dev Storage slot with the address of the current implementation.
   * This is the keccak-256 hash of "org.zeppelinos.proxy.implementation", and is
   * validated in the constructor.
   */
  bytes32 private constant IMPLEMENTATION_SLOT = 0x7050c9e0f4ca769c69bd3a8ef740bc37934f8e2c036e5a723fd8ee048ed3f8c3;

  /**
   * @dev Contract constructor.
   * @param _implementation Address of the initial implementation.
   */
  constructor(address _implementation) public {
    assert(IMPLEMENTATION_SLOT == keccak256("org.zeppelinos.proxy.implementation"));

    _setImplementation(_implementation);
  }

//   /**
//    * @dev Returns the current implementation.
//    * @return Address of the current implementation
//    */
  function _implementation() internal view override returns (address impl) {
    bytes32 slot = IMPLEMENTATION_SLOT;
    assembly {
      impl := sload(slot)
    }
  }

  /**
   * @dev Upgrades the proxy to a new implementation.
   * @param newImplementation Address of the new implementation.
   */
  function _upgradeTo(address newImplementation) internal {
    _setImplementation(newImplementation);
    emit Upgraded(newImplementation);
  }

  /**
   * @dev Sets the implementation address of the proxy.
   * @param newImplementation Address of the new implementation.
   */
  function _setImplementation(address newImplementation) private {
    require(AddressUtils.isContract(newImplementation), "Cannot set a proxy implementation to a non-contract address");

    bytes32 slot = IMPLEMENTATION_SLOT;

    assembly {
      sstore(slot, newImplementation)
    }
  }
}

// File: zos-lib/contracts/upgradeability/AdminUpgradeabilityProxy.sol

/**
 * @title AdminUpgradeabilityProxy
 * @dev This contract combines an upgradeability proxy with an authorization
 * mechanism for administrative tasks.
 * All external functions in this contract must be guarded by the
 * `ifAdmin` modifier. See ethereum/solidity#3864 for a Solidity
 * feature proposal that would enable this to be done automatically.
 */
contract AdminUpgradeabilityProxy is UpgradeabilityProxy {
  /**
   * @dev Emitted when the administration has been transferred.
   * @param previousAdmin Address of the previous admin.
   * @param newAdmin Address of the new admin.
   */
  event AdminChanged(address previousAdmin, address newAdmin);

  /**
   * @dev Storage slot with the admin of the contract.
   * This is the keccak-256 hash of "org.zeppelinos.proxy.admin", and is
   * validated in the constructor.
   */
  bytes32 private constant ADMIN_SLOT = 0x10d6a54a4754c8869d6886b5f5d7fbfa5b4522237ea5c60d11bc4e7a1ff9390b;

  /**
   * @dev Modifier to check whether the `msg.sender` is the admin.
   * If it is, it will run the function. Otherwise, it will delegate the call
   * to the implementation.
   */
  modifier ifAdmin() {
    if (msg.sender == _admin()) {
      _;
    } else {
      _fallback();
    }
  }

  /**
   * Contract constructor.
   * It sets the `msg.sender` as the proxy administrator.
   * @param _implementation address of the initial implementation.
   */
  constructor(address _implementation) UpgradeabilityProxy(_implementation) public {
    assert(ADMIN_SLOT == keccak256("org.zeppelinos.proxy.admin"));

    _setAdmin(msg.sender);
  }

  /**
   * @return The address of the proxy admin.
   */
  function admin() external view returns (address) {
    return _admin();
  }

  /**
   * @return The address of the implementation.
   */
  function implementation() external view returns (address) {
    return _implementation();
  }

  /**
   * @dev Changes the admin of the proxy.
   * Only the current admin can call this function.
   * @param newAdmin Address to transfer proxy administration to.
   */
  function changeAdmin(address newAdmin) external ifAdmin {
    require(newAdmin != address(0), "Cannot change the admin of a proxy to the zero address");
    emit AdminChanged(_admin(), newAdmin);
    _setAdmin(newAdmin);
  }

  /**
   * @dev Upgrade the backing implementation of the proxy.
   * Only the admin can call this function.
   * @param newImplementation Address of the new implementation.
   */
  function upgradeTo(address newImplementation) external ifAdmin {
    _upgradeTo(newImplementation);
  }

//   /**
//    * @dev Upgrade the backing implementation of the proxy and call a function
//    * on the new implementation.
//    * This is useful to initialize the proxied contract.
//    * @param newImplementation Address of the new implementation.
//    * @param data Data to send as msg.data in the low level call.
//    * It should include the signature and the parameters of the function to be
//    * called, as described in
//    * https://solidity.readthedocs.io/en/develop/abi-spec.html#function-selector-and-argument-encoding.
//    */
//   function upgradeToAndCall(address newImplementation, bytes data) payable external ifAdmin {
//     _upgradeTo(newImplementation);
//     require(address(this).call.value(msg.value)(data));
//   }

//   /**
//    * @return The admin slot.
//    */
  function _admin() internal view returns (address adm) {
    bytes32 slot = ADMIN_SLOT;
    assembly {
      adm := sload(slot)
    }
  }

  /**
   * @dev Sets the address of the proxy admin.
   * @param newAdmin Address of the new proxy admin.
   */
  function _setAdmin(address newAdmin) internal {
    bytes32 slot = ADMIN_SLOT;

    assembly {
      sstore(slot, newAdmin)
    }
  }

  /**
   * @dev Only fall back when the sender is not the admin.
   */
  function _willFallback() internal override{
    //require(msg.sender != _admin(), "Cannot call fallback function from the proxy admin");
    super._willFallback();
  }
}

/**
* Copyright CENTRE SECZ 2018
*
* Permission is hereby granted, free of charge, to any person obtaining a copy 
* of this software and associated documentation files (the "Software"), to deal 
* in the Software without restriction, including without limitation the rights 
* to use, copy, modify, merge, publish, distribute, sublicense, and/or sell 
* copies of the Software, and to permit persons to whom the Software is furnished to 
* do so, subject to the following conditions:
*
* The above copyright notice and this permission notice shall be included in all 
* copies or substantial portions of the Software.
*
* THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
* IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
* FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
* AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
* WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN 
* CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
*/

//pragma solidity ^0.5.0;


/**
 * @title RPGTokenProxy
 * @dev This contract proxies RPGToken calls and enables RPGToken upgrades
*/ 
contract RPGTokenProxy is AdminUpgradeabilityProxy {
    constructor(address _implementation) public AdminUpgradeabilityProxy(_implementation) {
    }
}

contract MutiSign is Ownable{
    address   g_CheckAddr; //楠岀鍦板潃
    
    //events
    event event_updateAddr(address addr);
    
    constructor(address addr) public {
        require(addr != address(0),'constructor addr can not be zero');

        g_CheckAddr = addr;
        emit event_updateAddr(g_CheckAddr);
    }
    
    //fallback
    // function () external payable
    // {
    //     revert();
    // }
    // fallback () external{
    //     revert();
    // }
    // receive() payable external {
    //     revert();
    // }
    
    function getCheckAddr() public view returns(address)
    {
        return g_CheckAddr;
    }
        
    function updateCheckAddr(address addr) public onlyOwner
    {
        require(addr !=  address(0),'updateCheckAddr addr can not be zero');
        
        g_CheckAddr = addr;
        emit event_updateAddr(g_CheckAddr);
    }
    
    function CheckWitness(bytes32 hashmsg,bytes memory signs) public view returns(bool)
    {
        require(signs.length == 65,'signs must = 65');
        
        address tmp = decode(hashmsg,signs);
        if(tmp == g_CheckAddr)
        {
            return true;
        }
        return false;
    }
    
    function decode(bytes32 hashmsg,bytes memory signedString) private pure returns (address)
    {
        bytes32  r = bytesToBytes32(slice(signedString, 0, 32));
        bytes32  s = bytesToBytes32(slice(signedString, 32, 32));
        byte  v = slice(signedString, 64, 1)[0];
        return ecrecoverDecode(hashmsg,r, s, v);
    }
  
    function slice(bytes memory data, uint start, uint len) private pure returns(bytes memory)
    {
        bytes memory b = new bytes(len);
        for(uint i = 0; i < len; i++){
            b[i] = data[i + start];
        }

        return b;
    }

    //浣跨敤ecrecover鎭㈠鍦板潃
    function ecrecoverDecode(bytes32 hashmsg,bytes32 r, bytes32 s, byte v1) private pure returns (address  addr){
        uint8 v = uint8(v1);
        if(uint8(v1)== 0 || uint8(v1)==1)
        {
            v = uint8(v1) + 27;
        }
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return address(0);
        }
        addr = ecrecover(hashmsg, v, r, s);
    }

    //bytes杞崲涓篵ytes32
    function bytesToBytes32(bytes memory source) private pure returns (bytes32 result) {
        assembly {
            result := mload(add(source, 32))
        }
    }
    
    // function strConcat(string memory _a, string memory _b) internal pure returns (string memory){
    //     bytes memory _ba = bytes(_a);
    //     bytes memory _bb = bytes(_b);
    //     string memory ret = new string(_ba.length + _bb.length);
    //     bytes memory bret = bytes(ret);
    //     uint k = 0;
    //     for (uint i = 0; i < _ba.length; i++)
    //         bret[k++] = _ba[i];
    //     for (uint i = 0; i < _bb.length; i++)
    //         bret[k++] = _bb[i];
        
    //     return string(ret);
    // }
    
}

contract MutiSign_CM is Ownable{
    address[]   public g_CheckAddrs; //验签地址,0是创始地址，不可替�?
    mapping(address => uint256) public g_Expired;
    
    //events
    event event_addAddr(address addr,uint256 expire);
    event event_delAddr(address addr);
    
    constructor() public {
    }

    function init(address owner,address groupid) external {
        require(owner != address(0) ,'init para owner err');

        initOwner(owner);
        g_CheckAddrs.push(groupid);
        g_Expired[groupid] = block.timestamp+3153600000;    //86400*365*100,100 years
    }
    
    //fallback
    //function () external payable{
    //    revert();
    //}
    
    function AddCheckGroup(address addr,uint256 expire,bytes calldata signs) external {
        require(addr !=  address(0)      ,'AddCheckGroup addr can not be zero');
        require(expire > block.timestamp ,'AddCheckGroup expire must > now');
        require(signs.length >= 65       ,'AddCheckGroup signs length err');
        
        for(uint256 i = 0 ; i < g_CheckAddrs.length; i++){
            require(g_CheckAddrs[i] != addr,'AddCheckGroup addr existed');
        }

        //check sign
        bytes32 hashmsg = keccak256(abi.encodePacked(addr,expire));
        address tmp = decode(hashmsg,signs);
        require(tmp == g_CheckAddrs[0],'AddCheckGroup check sign failed');

        g_CheckAddrs.push(addr);
        g_Expired[addr] = expire;
        emit event_addAddr(addr,expire);
    }
    
    function DelCheckGroup(address addr) public onlyOwner{
        require(addr !=  address(0)      ,'DelCheckGroup addr can not be zero');

        for(uint256 i = 0 ; i < g_CheckAddrs.length; i++){
            if(g_CheckAddrs[i] == addr){
                g_CheckAddrs[i] = address(0);
                g_Expired[g_CheckAddrs[i]] = 0;
                emit event_delAddr(addr);
                return;
            }
        }
    }
    
    function CheckWitness(bytes32 hashmsg,bytes memory signs,address groupId) public view returns(bool,bool){
        require(signs.length == 65,'signs must = 65');
        
        address tmp = decode(hashmsg,signs);

        for(uint256 i = 0 ; i < g_CheckAddrs.length; i++){
            if(tmp == g_CheckAddrs[i] && tmp == groupId){
                return (true,g_Expired[tmp]>=block.timestamp);
            }
        }
        return (false,false);
    }
    
    function decode(bytes32 hashmsg,bytes memory signedString) private pure returns (address)
    {
        bytes32  r = bytesToBytes32(slice(signedString, 0, 32));
        bytes32  s = bytesToBytes32(slice(signedString, 32, 32));
        byte  v = slice(signedString, 64, 1)[0];
        return ecrecoverDecode(hashmsg,r, s, v);
    }
  
    function slice(bytes memory data, uint start, uint len) private pure returns(bytes memory)
    {
        bytes memory b = new bytes(len);
        for(uint i = 0; i < len; i++){
            b[i] = data[i + start];
        }

        return b;
    }

    //使用ecrecover恢复地址
    function ecrecoverDecode(bytes32 hashmsg,bytes32 r, bytes32 s, byte v1) private pure returns (address  addr){
        uint8 v = uint8(v1);
        if(uint8(v1)== 0 || uint8(v1)==1)
        {
            v = uint8(v1) + 27;
        }
        if (uint256(s) > 0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF5D576E7357A4501DDFE92F46681B20A0) {
            return address(0);
        }
        addr = ecrecover(hashmsg, v, r, s);
    }

    //bytes转换为bytes32
    function bytesToBytes32(bytes memory source) private pure returns (bytes32 result) {
        assembly {
            result := mload(add(source, 32))
        }
    }
    
    function SetGroupId(address addr,uint256 pos,uint256 expire) external onlyOwner{
        if(g_CheckAddrs.length >= pos+1) {
            g_CheckAddrs[pos] = addr;
        }else{
            g_CheckAddrs.push(addr);
        }
        g_Expired[addr] = expire;
    }
    
}

contract EventConfig is Ownable {
    struct cfg {
        string chainid;
        string contractaddr;
        string eventname;
    }
    mapping(string => cfg[]) public g_Events;
    //cfg[] public g_Cfg;

    function init(address addr,string[] memory businame,string[][] memory chainid,string[][] memory contractaddr,string[][] memory eventname) external {
        initOwner(addr);

        for(uint256 i = 0 ; i < businame.length; i++){
            for(uint256 j = 0 ; j < chainid.length; j++){
                for(uint k = 0 ; k < chainid[i].length; k++){
                    cfg memory c;
                    c.chainid = chainid[j][k];
                    c.contractaddr = contractaddr[j][k];
                    c.eventname = eventname[j][k];
                    g_Events[businame[i]].push(c);
                }
            }
        }
    }

    function AddCfg(string memory businame,string memory chainid,string memory contractaddr,string memory eventname) onlyOwner external {
        require(bytes(businame).length > 0      ,'AddCfg businame err');
        require(bytes(chainid).length > 0       ,'AddCfg chainid err');
        require(bytes(contractaddr).length > 0  ,'AddCfg contractaddr err');
        require(bytes(eventname).length > 0     ,'AddCfg eventname err');

        cfg memory c;
        c.chainid = chainid;
        c.contractaddr = contractaddr;
        c.eventname = eventname;
        g_Events[businame].push(c);
    }

    function DelCfg(string memory businame,string memory chainid,string memory contractaddr,string memory eventname) onlyOwner external returns(bool){
        for(uint256 i = 0 ; i < g_Events[businame].length;i++){
            if(keccak256(bytes(chainid)) == keccak256(bytes(g_Events[businame][i].chainid))
            && keccak256(bytes(contractaddr)) == keccak256(bytes(g_Events[businame][i].contractaddr))
            && keccak256(bytes(eventname)) == keccak256(bytes(g_Events[businame][i].eventname))
            ){
                g_Events[businame][i].chainid = "";
                g_Events[businame][i].contractaddr = "";
                g_Events[businame][i].eventname = "";
                return true;
            }
        }
        return false;
    }

    function IsValidEvent(string memory businame,string memory chainid,string memory contractaddr,string memory eventname) external view returns(bool){
        for(uint256 i = 0 ; i < g_Events[businame].length;i++){
            if(keccak256(bytes(chainid)) == keccak256(bytes(g_Events[businame][i].chainid))
            && keccak256(bytes(contractaddr)) == keccak256(bytes(g_Events[businame][i].contractaddr))
            && keccak256(bytes(eventname)) == keccak256(bytes(g_Events[businame][i].eventname))
            ){
                return true;
            }
        }
        return false;
    }
}

contract CrossContract{
    using SafeERC20 for IERC20;
    
    string      public  g_Name;
    address     public  g_Setter;           //it should be gnosis addr
    address     payable public g_FeeAddr;
    MutiSign    public  g_MutiSignContract;
    uint256     public  g_iNonce = 0;
    address     public  g_RPG;
    mapping(bytes32 => bool) public g_Workedmap;
    MutiSign_CM public g_MutiSignContract_CM;
    string      public g_BusiName;
    EventConfig public g_EventConfigContract;
    CrossContractEx public g_CrossEx;
    address[]   public g_pool_fts;

    //events
    event event_init(string name,address addr,address setter,address feeaddr);
    event event_nonce(uint256 nonce);
    event event_RangersSpeedUp(address fromAsset,bytes hash,address sender,uint256 fee);
    
    event event_CrossErc20(         uint256 fee,address from,address to,string tochain,address sender,address toaddr,uint256 amount);
    event event_CrossErc20_Failed(  uint256 fee,address from,address to,string tochain,address sender,address toaddr,uint256 amount);
    event event_CrossErc721(        uint256 fee,address from,address to,string tochain,address sender,address toaddr,uint256 nftid);
    event event_CrossErc721_Failed( uint256 fee,address from,address to,string tochain,address sender,address toaddr,uint256 nftid);
    
    event event_withdrawErc20(          address from,string fromchain,address to,address user,uint256 amount);
    event event_withdrawErc20_Failed(   address from,string fromchain,address to,address user,uint256 amount);
    event event_withdrawErc721(         address from,string fromchain,address to,address user,uint256 nftid);
    event event_withdrawErc721_Failed(  address from,string fromchain,address to,address user,uint256 nftid);
    
    //CM
    event event_CrossErc20_CM(         uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256 amount);
    event event_CrossErc20_Failed_CM(  uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256 amount);
    event event_CrossErc721_CM(        uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256 nftid);
    event event_CrossErc721_Failed_CM( uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256 nftid);
    event event_CrossErc721_CM_Batch(  uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256[] nftids);
    event event_CrossErc1155_CM(       uint256 fee,address from,address to,uint256 tochainId,address sender,address toaddr,uint256[] nftids,uint256[] values);
    
    event event_withdrawErc20_CM(          address from,uint256 fromchainId,address to,address user,uint256 amount);
    event event_withdrawErc20_Failed_CM(   address from,uint256 fromchainId,address to,address user,uint256 amount);
    event event_withdrawErc721_CM(         address from,uint256 fromchainId,address to,address user,uint256 nftid);
    event event_withdrawErc721_Failed_CM(  address from,uint256 fromchainId,address to,address user,uint256 nftid);
    event event_withdrawErc1155_CM(        address from,uint256 fromchainId,address to,address user,uint256[] id,uint256[] value);

    //CM2
    event event_CrossErc20_CM2(         uint256 fee,address from,string to,uint256 tochainId,address sender,string toaddr,uint256 amount);
    event event_CrossErc20_Failed_CM2(  uint256 fee,address from,string to,uint256 tochainId,address sender,string toaddr,uint256 amount);

    event event_withdrawErc20_CM2(          address from,uint256 fromchainId,bytes to,address user,uint256 amount);
    event event_withdrawErc20_Failed_CM2(   address from,uint256 fromchainId,bytes to,address user,uint256 amount);
    
    // event e_dbg(address msg);
    // event e_dbg(uint256 msg);
    // event e_dbg(string msg);
    // event e_dbg(bytes msg);
    // event e_dbg(bytes32 msg);

    //fallback
    //function () external payable
    fallback () external
    {
        
    }

    receive() payable external 
    {
        require(msg.value > 0,'fallback require msg.value > 0');
        g_FeeAddr.transfer(msg.value);
        
        bytes memory txHash;
        emit event_RangersSpeedUp(address(0) , txHash , msg.sender , msg.value);
    }
    
    function init(string memory _name,address payable _addr,address _setter,address payable _feeaddr,address payable _rpg,address _muti_cm,address ec,address ex) public {
        require(bytes(_name).length > 0                ,'must has name');
        require(_addr != address(0)                    ,'_addr');
        require(_setter != address(0)                  ,'_setter');
        require(_feeaddr != address(0)                 ,'_feeaddr');
        
        if(address(g_MutiSignContract)!=address(0)) {
            require(msg.sender == g_Setter, 'init not setter calling');
        }
        
        g_Name = _name;
        g_MutiSignContract = MutiSign(_addr);
        g_Setter = _setter;
        g_FeeAddr = _feeaddr;
        g_RPG = _rpg;
        g_MutiSignContract_CM = MutiSign_CM(_muti_cm);
        g_BusiName = "Bridge";
        g_EventConfigContract = EventConfig(ec);
        g_CrossEx = CrossContractEx(ex);
        emit event_init(_name,_addr,_setter,_feeaddr);
    }
    
    function getnonce() public
    {
        emit event_nonce(g_iNonce);
    }

    function IsInPoolfts(address addr) private view returns(bool) {
        for(uint256 i = 0; i < g_pool_fts.length; i++) {
            if(g_pool_fts[i] == addr){
                return true;
            }
        }
        return false;
    }

    function AddPoolFts(address[] memory addr) external{
        require(msg.sender == g_Setter  ,'p1');

        for(uint256 i=0;i<addr.length; i++){
            if(IsInPoolfts(addr[i]) == false){
                g_pool_fts.push(addr[i]);
            }
        }
    }
    
    function DelPoolFts(address addr) external{
        require(msg.sender == g_Setter  ,'p1');

        for(uint256 i = 0; i < g_pool_fts.length; i++) {
            if(g_pool_fts[i] == addr){
                g_pool_fts[i] = address(0);
                return;
            }
        }
    }

    // function speedUp(address fromAsset,bytes calldata txHash, uint256 fee) external payable {
    //     if(fromAsset == address(0)) {
    //         require(msg.value == fee,"speedUp insufficient fee num");
    //         g_FeeAddr.transfer(msg.value);
    //     }else{
    //         IERC20(fromAsset).safeTransferFrom(msg.sender, g_FeeAddr, fee);
    //     }
        
    //     emit event_RangersSpeedUp(fromAsset , txHash, msg.sender , fee);
    // }
    
    ///do cross////////////////////////////////////////////////////////////////////////////
    // function DoCrossErc20(address _fromcontract,address _tocontract,string calldata _toChain,address _fromaddr,address _toaddr,uint256 amount) payable external{
    //     require(_fromcontract != address(0)                     ,'p1');
    //     require(_tocontract != address(0)                       ,'p2');
    //     require(bytes(_toChain).length != 0                     ,'p3');
    //     //require(_fromaddr != address(0)                         ,'p4');
    //     require(_toaddr != address(0)                           ,'p5');
    //     require(amount > 0                                      ,'p6');
    //     require(msg.value > 0                                   ,'no fee');
    //     require(msg.sender == _fromaddr                         ,'p4');
        
    //     g_FeeAddr.transfer(msg.value);
        
    //     if(IERC20(_fromcontract).balanceOf(_fromaddr) >= amount && IERC20(_fromcontract).allowance(_fromaddr,address(this)) >= amount) {
    //         IERC20(_fromcontract).safeTransferFrom(_fromaddr,address(this),amount);
    //         emit event_CrossErc20(msg.value,_fromcontract,_tocontract,_toChain,_fromaddr,_toaddr,amount);
    //         return;
    //     }

    //     emit event_CrossErc20_Failed(msg.value,_fromcontract,_tocontract,_toChain,_fromaddr,_toaddr,amount);
    //     return;
    // }
    
    // function DoCrossErc721(address _fromcontract,address _tocontract,string calldata _toChain,address _fromaddr,address _toaddr,uint256 _nftid) payable external{
    //     require(_fromcontract != address(0)                     ,'p1');
    //     require(_tocontract != address(0)                       ,'p2');
    //     require(bytes(_toChain).length != 0                     ,'p3');
    //     //require(_fromaddr != address(0)                         ,'p4 0');
    //     require(_toaddr != address(0)                           ,'p5');
    //     require(msg.value > 0                                   ,'no fee');
    //     require(msg.sender == _fromaddr                         ,'p4');
        
    //     g_FeeAddr.transfer(msg.value);
        
    //     if(IERC721(_fromcontract).ownerOf(_nftid) == _fromaddr && (IERC721(_fromcontract).getApproved(_nftid) == address(this) || IERC721(_fromcontract).isApprovedForAll(_fromaddr,address(this))==true )) {
    //         IERC721(_fromcontract).transferFrom(_fromaddr,address(this),_nftid);
    //         emit event_CrossErc721(msg.value,_fromcontract,_tocontract,_toChain,_fromaddr,_toaddr,_nftid);
    //         return;
    //     }

    //     emit event_CrossErc721_Failed(msg.value,_fromcontract,_tocontract,_toChain,_fromaddr,_toaddr,_nftid);
    //     return;
    // }
    
    
    ///withdraw action////////////////////////////////////////////////////////////////////////////
    // function WithdrawErc20(uint256 nonce,address _fromcontract,string calldata _fromchain,address _tocontract,address payable _addr,uint256 _amount,bytes calldata _signs) external
    // {
    //     require(g_iNonce+1 == nonce                             ,'nonce');
    //     require(_fromcontract != address(0)                     ,'p2');
    //     require(_tocontract != address(0)                       ,'p4');
    //     //require(bytes(_fromchain).length != 0                   ,'p3 null');
    //     require(keccak256(bytes(_fromchain))==keccak256(bytes(g_Name))	,'p3');
    //     require(_addr != address(0)                             ,'p5');
    //     require(_signs.length == 65                             ,'p7');

    //     bytes memory str = abi.encodePacked(nonce,_fromcontract,_fromchain,_tocontract,_addr,_amount);
    //     bytes32 hashmsg = keccak256(str);

    //     if(!g_MutiSignContract.CheckWitness(hashmsg,_signs))
    //     {
    //         //revert("Withdraw CheckWitness failed");     //revert can make call failed ,but can't punish bad gays
    //         return;
    //     }
        
    //     g_iNonce++;
    //     emit event_nonce(g_iNonce);
        
    //     if(IERC20(_fromcontract).balanceOf(address(this)) >= _amount) {
    //         IERC20(_fromcontract).safeTransfer(_addr,_amount);
    //         emit event_withdrawErc20(_fromcontract,_fromchain,_tocontract,_addr,_amount);
    //         return;
    //     }

    //     emit event_withdrawErc20_Failed(_fromcontract,_fromchain,_tocontract,_addr,_amount);
    //     return;
    // }

    // function TryownerOf(address _fromcontract,uint256 _nftid) view external returns(bool){
    //     if(IERC721(_fromcontract).ownerOf(_nftid) == address(this)){
    //         return true;
    //     }
    //     return false;
    // }

    // function WithdrawErc721(uint256 nonce,address _fromcontract,string calldata _fromchain,address _tocontract,address payable _addr,uint256 _nftid,bytes calldata signs) external
    // {
    //     require(g_iNonce+1 == nonce                             ,'nonce');
    //     require(_fromcontract != address(0)                     ,'p2');
    //     require(_tocontract != address(0)                       ,'p4');
    //     //require(bytes(_fromchain).length != 0                   ,'_fromchain null');
    //     require(keccak256(bytes(_fromchain))==keccak256(bytes(g_Name))	,'p3');
    //     require(_addr != address(0)                             ,'_addr');
    //     require(signs.length == 65                              ,'p7');

    //     bytes memory str = abi.encodePacked(nonce,_fromcontract,_fromchain,_tocontract,_addr,_nftid);
    //     bytes32 hashmsg = keccak256(str);

    //     if(!g_MutiSignContract.CheckWitness(hashmsg,signs))
    //     {
    //         //revert("Withdraw CheckWitness failed");     //revert can make call failed ,but can't punish bad gays
    //         return;
    //     }
        
    //     g_iNonce++;
    //     emit event_nonce(g_iNonce);
        
    //     bool ok;
    //     try g_CrossEx.TryownerOf(_fromcontract,_nftid,address(this)) returns(bool v) {    
    //         ok = v;
    //     }catch{
    //         ok = false;
    //     }
    //     if(ok == true){
    //         IERC721(_fromcontract).transferFrom(address(this),_addr,_nftid);
    //         emit event_withdrawErc721(_fromcontract,_fromchain,_tocontract,_addr,_nftid);
    //         return;
    //     }else{
    //         IERC721(_fromcontract).mint(_addr,_nftid);
    //         emit event_withdrawErc721(_fromcontract,_fromchain,_tocontract,_addr,_nftid);
    //         return;
    //     }
        
    //     //???emit event_withdrawErc721_Failed(_fromcontract,_fromchain,_tocontract,_addr,_nftid);
    // }

		///CM////////////////////////////////////////////////////////////////////////////
    function DoCrossErc20_CM(address _fromcontract,address _tocontract,uint256 _toChainId,address _fromaddr,address _toaddr,uint256 amount) payable external{
        require(_fromcontract != address(0)                     ,'p1');
        require(_tocontract != address(0)                       ,'p2');
        require(_toChainId != 0                                 ,'p3');
        //require(_fromaddr != address(0)                         ,'p4');
        require(_toaddr != address(0)                           ,'p5');
        require(amount > 0                                      ,'p6');
        require(msg.value > 0                                   ,'no fee');
        require(msg.sender == _fromaddr                         ,'p4');

        g_FeeAddr.transfer(msg.value);
        
        uint256 am = g_CrossEx.FormatDecimal(amount,IERC20(_fromcontract).decimals(),18);
        // uint256 am = amount;
        // uint8   dec = IERC20(_fromcontract).decimals();
        // if(dec < 18){
        //     for(uint256 i = dec ; i < 18; i++ ){
        //         am = am*10;
        //     }
        // }else if(dec > 18){
        //     for(uint256 i = 18 ; i < dec; i++ ){
        //         am = am/10;
        //     }
        // }

        if(IERC20(_fromcontract).balanceOf(_fromaddr) >= amount && IERC20(_fromcontract).allowance(_fromaddr,address(this)) >= amount) {
            IERC20(_fromcontract).safeTransferFrom(_fromaddr,address(this),amount);
            //if(g_RPG != address(0) && _fromcontract == g_RPG) {
            if(IsInPoolfts(_fromcontract) == false){
                IERC20(_fromcontract).burn(address(this),amount);
            }
            emit event_CrossErc20_CM(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,am);
            return;
        }

        emit event_CrossErc20_Failed_CM(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,am);
        return;
    }

    function DoCrossErc20_CM2(address _fromcontract,string memory _tocontract,uint256 _toChainId,address _fromaddr,string memory _toaddr,uint256 amount) payable external{
        require(_fromcontract != address(0)                     ,'p1');
        require(bytes(_tocontract).length > 0                   ,'p2');
        require(_toChainId != 0                                 ,'p3');
        //require(_fromaddr != address(0)                         ,'p4');
        require(bytes(_toaddr).length > 0                       ,'p5');
        require(amount > 0                                      ,'p6');
        require(msg.value > 0                                   ,'no fee');
        require(msg.sender == _fromaddr                         ,'p4');

        g_FeeAddr.transfer(msg.value);
        
        uint256 am = amount;
        //uint8   dec = IERC20(_fromcontract).decimals();
        if(_toChainId == 115998 || _toChainId == 115999){
            am = g_CrossEx.FormatDecimal(amount,IERC20(_fromcontract).decimals(),9);
            // if(dec < 9){
            //     for(uint256 i = dec ; i < 9; i++ ){
            //         am = am*10;
            //     }
            // }else if(dec > 9){
            //     for(uint256 i = 9 ; i < dec; i++ ){
            //         am = am/10;
            //     }
            // }
        }else{
            am = g_CrossEx.FormatDecimal(amount,IERC20(_fromcontract).decimals(),18);
            // if(dec < 18){
            //     for(uint256 i = dec ; i < 18; i++ ){
            //         am = am*10;
            //     }
            // }else if(dec > 18){
            //     for(uint256 i = 18 ; i < dec; i++ ){
            //         am = am/10;
            //     }
            // }
        }

        if(IERC20(_fromcontract).balanceOf(_fromaddr) >= amount && IERC20(_fromcontract).allowance(_fromaddr,address(this)) >= amount) {
            IERC20(_fromcontract).safeTransferFrom(_fromaddr,address(this),amount);
            //if(g_RPG != address(0) && _fromcontract == g_RPG) {
            if(IsInPoolfts(_fromcontract) == false){
                IERC20(_fromcontract).burn(address(this),amount);
            }
            emit event_CrossErc20_CM2(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,am);
            return;
        }

        emit event_CrossErc20_Failed_CM2(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,am);
        return;
    }
    
    function DoCrossErc721_CM(address _fromcontract,address _tocontract,uint256 _toChainId,address _fromaddr,address _toaddr,uint256 _nftid) payable external{
        require(_fromcontract != address(0)                     ,'p1');
        require(_tocontract != address(0)                       ,'p2');
        require(_toChainId != 0                                 ,'p3');
        //require(_fromaddr != address(0)                         ,'p4');
        require(_toaddr != address(0)                           ,'p5');
        require(msg.value > 0                                   ,'no fee');
        require(msg.sender == _fromaddr                         ,'p4');
        
        g_FeeAddr.transfer(msg.value);
        
        if(IERC721(_fromcontract).ownerOf(_nftid) == _fromaddr && (IERC721(_fromcontract).getApproved(_nftid) == address(this) || IERC721(_fromcontract).isApprovedForAll(_fromaddr,address(this))==true )) {
            IERC721(_fromcontract).transferFrom(_fromaddr,address(this),_nftid);
            emit event_CrossErc721_CM(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,_nftid);
            return;
        }

        emit event_CrossErc721_Failed_CM(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,_nftid);
        return;
    }

    function DoCrossErc721_CM_Batch(address _fromcontract,address _tocontract,uint256 _toChainId,address _fromaddr,address _toaddr,uint256[] memory _nftids) payable external{
        require(_fromcontract != address(0)                     ,'p1');
        require(_tocontract != address(0)                       ,'p2');
        require(_toChainId != 0                                 ,'p3');
        //require(_fromaddr != address(0)                         ,'p4');
        require(_toaddr != address(0)                           ,'p5');
        require(msg.value > 0                                   ,'no fee');
        require(msg.sender == _fromaddr                         ,'p4');
        require(_nftids.length <= 30                            ,'>30');
        
        g_FeeAddr.transfer(msg.value);

        for(uint256 i = 0 ; i < _nftids.length ; i++) {
            require(IERC721(_fromcontract).ownerOf(_nftids[i]) == _fromaddr,'ownerOf err');
            require(IERC721(_fromcontract).getApproved(_nftids[i]) == address(this) || IERC721(_fromcontract).isApprovedForAll(_fromaddr,address(this))==true,'approve err');

            IERC721(_fromcontract).transferFrom(_fromaddr,address(this),_nftids[i]);
        }
        event_CrossErc721_CM_Batch(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,_nftids);
        
        return;
    }
    
    ///CM withdraw action////////////////////////////////////////////////////////////////////////////
    // function verifymsg(bytes32 hashmsg,bytes memory signs,address groupId) private view returns(bool){
    //     (bool result,bool alive) = g_MutiSignContract_CM.CheckWitness(hashmsg,signs,groupId);
    //     return (result == true && alive == true);
    // }

    // function DoWithdrawErc20Transfer(uint256 dec,bytes32 nonce,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _amount) internal {
    //     uint256 am = g_CrossEx.FormatDecimal(_amount, dec , IERC20(_fromcontract).decimals());
    //     //uint256 am = _amount;
    //     // if(IERC20(_fromcontract).decimals() < dec){
    //     //     for(uint256 i = IERC20(_fromcontract).decimals() ; i < dec; i++ ){
    //     //         am = am/10;
    //     //     }
    //     // }else if(IERC20(_fromcontract).decimals() > dec){
    //     //     for(uint256 i = dec ; i < IERC20(_fromcontract).decimals(); i++ ){
    //     //         am = am*10;
    //     //     }
    //     // }
        
    //     if(g_RPG != address(0) && _fromcontract == g_RPG){
    //         IERC20(g_RPG).mint(address(this),am);
    //     }

    //     if(IERC20(_fromcontract).balanceOf(address(this)) >= am) {
    //         IERC20(_fromcontract).safeTransfer(_addr,am);
    //         g_Workedmap[nonce] = true;
    //         emit event_withdrawErc20_CM(_fromcontract,_fromchainId,_tocontract,_addr,am);
    //         return;
    //     }

    //     emit event_withdrawErc20_Failed_CM(_fromcontract,_fromchainId,_tocontract,_addr,am);
    //     return;
    // }

    function WithdrawErc20_CM(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _amount,address _groupId,bytes calldata _signs) external
    {
        require(g_Workedmap[nonce] == false                     ,'p1');
        require(_fromcontract != address(0)                     ,'p5');
        require(_tocontract != address(0)                       ,'p7');
        require(_addr != address(0)                             ,'p8');
        require(_groupId != address(0)                          ,'p10');
        require(_signs.length == 65                             ,'p11');
        uint256 am;
        assembly {
            am := chainid()
        }
        require(am==_fromchainId                                ,'p6');
        require(g_EventConfigContract.IsValidEvent(g_BusiName,fromchainid,frombridgecontract,eventname)==true,'IsValidEvent err');

        if (g_CrossEx.VerifyCrossErc20Sign(nonce,fromchainid,frombridgecontract,eventname,_fromcontract,_fromchainId,_tocontract,_addr,_amount,_groupId,_signs) == false){
            return;
        }

        am = g_CrossEx.FormatDecimal(_amount, 18 , IERC20(_fromcontract).decimals());
        //if(g_RPG != address(0) && _fromcontract == g_RPG){
        if(IsInPoolfts(_fromcontract) == false){
            IERC20(_fromcontract).mint(address(this),am);
        }

        if(IERC20(_fromcontract).balanceOf(address(this)) >= am) {
            IERC20(_fromcontract).safeTransfer(_addr,am);
            g_Workedmap[nonce] = true;
            emit event_withdrawErc20_CM(_fromcontract,_fromchainId,_tocontract,_addr,am);
            return;
        }

        emit event_withdrawErc20_Failed_CM(_fromcontract,_fromchainId,_tocontract,_addr,am);

        //DoWithdrawErc20Transfer(18,nonce,_fromcontract,_fromchainId,_tocontract,_addr,_amount);
        return;
    }

    // function DoWithdrawErc20Transfer2(uint256 dec,bytes32 nonce,address _fromcontract,uint256 _fromchainId,bytes memory _tocontract,address payable _addr,uint256 _amount) internal {
    //     uint256 am = g_CrossEx.FormatDecimal(_amount, dec , IERC20(_fromcontract).decimals());
    //     // uint256 am = _amount;
    //     // if(IERC20(_fromcontract).decimals() < dec){
    //     //     for(uint256 i = IERC20(_fromcontract).decimals() ; i < dec; i++ ){
    //     //         am = am/10;
    //     //     }
    //     // }else if(IERC20(_fromcontract).decimals() > dec){
    //     //     for(uint256 i = dec ; i < IERC20(_fromcontract).decimals(); i++ ){
    //     //         am = am*10;
    //     //     }
    //     // }
        
    //     if(g_RPG != address(0) && _fromcontract == g_RPG){
    //         IERC20(g_RPG).mint(address(this),am);
    //     }

    //     if(IERC20(_fromcontract).balanceOf(address(this)) >= am) {
    //         IERC20(_fromcontract).safeTransfer(_addr,am);
    //         g_Workedmap[nonce] = true;
    //         emit event_withdrawErc20_CM2(_fromcontract,_fromchainId,_tocontract,_addr,am);
    //         return;
    //     }

    //     emit event_withdrawErc20_Failed_CM2(_fromcontract,_fromchainId,_tocontract,_addr,am);
    //     return;
    // }

    function WithdrawErc20_CM2(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,bytes memory _tocontract,address payable _addr,uint256 _amount,address _groupId,bytes calldata _signs) external
    {
        require(g_Workedmap[nonce] == false                     ,'p1');
        require(_fromcontract != address(0)                     ,'p5');
        require(_tocontract.length > 0                          ,'p7');
        require(_addr != address(0)                             ,'p8');
        require(_groupId != address(0)                          ,'p10');
        require(_signs.length == 65                             ,'p11');
        uint256 am;
        assembly {
            am := chainid()
        }
        require(am==_fromchainId                                ,'p6');
        require(g_EventConfigContract.IsValidEvent(g_BusiName,fromchainid,frombridgecontract,eventname)==true,'IsValidEvent err');

        // bytes memory str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_amount,_groupId);
        // bytes32 hashmsg = keccak256(str);

        // if(verifymsg(hashmsg,_signs,_groupId) == false)
        // {
        //     return;
        // }
        if(g_CrossEx.VerifyCrossErc20Sign2(nonce,fromchainid,frombridgecontract,eventname,_fromcontract,_fromchainId,_tocontract,_addr,_amount,_groupId,_signs) == false){
            return;
        }

        am = g_CrossEx.FormatDecimal(_amount, 9 , IERC20(_fromcontract).decimals());
        //if(g_RPG != address(0) && _fromcontract == g_RPG){
        if(IsInPoolfts(_fromcontract) == false){
            IERC20(_fromcontract).mint(address(this),am);
        }

        if(IERC20(_fromcontract).balanceOf(address(this)) >= am) {
            IERC20(_fromcontract).safeTransfer(_addr,am);
            g_Workedmap[nonce] = true;
            emit event_withdrawErc20_CM2(_fromcontract,_fromchainId,_tocontract,_addr,am);
            return;
        }

        emit event_withdrawErc20_Failed_CM2(_fromcontract,_fromchainId,_tocontract,_addr,am);

        //DoWithdrawErc20Transfer2(9,nonce,_fromcontract,_fromchainId,_tocontract,_addr,_amount);
        return;
    }

    // function VerifyCrossErc721Sign(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _nftid,address _groupId,bytes calldata signs) private view returns(bool){
    //     bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
    //     bytes32 magic = keccak256(str);

    //     str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_nftid,_groupId,magic);
    //     bytes32 hashmsg = keccak256(str);

    //     if(verifymsg(hashmsg,signs,_groupId) == false){
    //         return false;
    //     }
    //     return true;
    // }

    function WithdrawErc721_CM(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _nftid,address _groupId,bytes calldata signs) external
    {
        require(g_Workedmap[nonce] == false                     ,'p1');
        require(_fromcontract != address(0)                     ,'p5');
        require(_tocontract != address(0)                       ,'p7');
        require(_addr != address(0)                             ,'p8');
        require(_groupId != address(0)                          ,'p10');
        require(signs.length == 65                              ,'p11');
        uint chainId;
        assembly {
            chainId := chainid()
        }
        require(chainId==_fromchainId                           ,'p6');
        require(g_EventConfigContract.IsValidEvent(g_BusiName,fromchainid,frombridgecontract,eventname)==true,'IsValidEvent err');

        // bytes memory str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_nftid,_groupId);
        // bytes32 hashmsg = keccak256(str);
        // if(verifymsg(hashmsg,signs,_groupId) == false)
        // {
        //     //revert("Withdraw CheckWitness failed");     //revert can make call failed ,but can't punish bad gays
        //     return;
        // }
        //if(g_CrossEx.VerifyCrossErc721Sign(nonce,fromchainid,frombridgecontract,eventname,_fromcontract,_fromchainId,_tocontract,_addr,_nftid,_groupId,signs) == false){
        if(g_CrossEx.VerifyCrossErc20Sign(nonce,fromchainid,frombridgecontract,eventname,_fromcontract,_fromchainId,_tocontract,_addr,_nftid,_groupId,signs) == false){
            return;
        }
        
        bool ok;
        try g_CrossEx.TryownerOf(_fromcontract,_nftid,address(this)) returns(bool v) {    
            ok = v;
        }catch{
            ok = false;
        }
        if(ok == true){
            IERC721(_fromcontract).transferFrom(address(this),_addr,_nftid);
            g_Workedmap[nonce] == true;
            emit event_withdrawErc721_CM(_fromcontract,_fromchainId,_tocontract,_addr,_nftid);
            return;
        }else{
            IERC721(_fromcontract).mint(_addr,_nftid);
            g_Workedmap[nonce] == true;
            emit event_withdrawErc721_CM(_fromcontract,_fromchainId,_tocontract,_addr,_nftid);
            return;
        }

        //???emit event_withdrawErc721_Failed_CM(_fromcontract,_fromchainId,_tocontract,_addr,_nftid);
    }

    function WithdrawErc721_CM_batch(bytes32 nonce,stmagic memory m,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256[] memory _nftids,address _groupId,bytes calldata signs) external
    {
        require(g_Workedmap[nonce] == false                     ,'p1');
        require(_fromcontract != address(0)                     ,'p3');
        require(_tocontract != address(0)                       ,'p5');
        require(_addr != address(0)                             ,'p6');
        require(_groupId != address(0)                          ,'p8');
        require(signs.length == 65                              ,'p9');
        uint chainId;
        assembly {
            chainId := chainid()
        }
        require(chainId==_fromchainId                           ,'p4');
        require(g_EventConfigContract.IsValidEvent(g_BusiName,m.fromchainid,m.frombridgecontract,m.eventname)==true,'IsValidEvent err');

        require(g_CrossEx.VerifyCrossErc721Sign_batch(nonce,m.fromchainid,m.frombridgecontract,m.eventname,_fromcontract,_fromchainId,_tocontract,_addr,_nftids,_groupId,signs) == true,'verify failed');
        // if (g_CrossEx.VerifyCrossErc721Sign_batch(nonce,m.fromchainid,m.frombridgecontract,m.eventname,_fromcontract,_fromchainId,_tocontract,_addr,_nftids,_groupId,signs) == false){
        //     return ;
        // }
        for(uint256 i = 0 ; i < _nftids.length; i++){
            bool ok;
            try g_CrossEx.TryownerOf(_fromcontract,_nftids[i],address(this)) returns(bool v) {    
                ok = v;
            }catch{
                ok = false;
            }
            if(ok == true){
                IERC721(_fromcontract).transferFrom(address(this),_addr,_nftids[i]);
            }else{
                IERC721(_fromcontract).mint(_addr,_nftids[i]);
            }
            require(g_CrossEx.TryownerOf(_fromcontract, _nftids[i], _addr) == true);
            emit event_withdrawErc721_CM(_fromcontract,_fromchainId,_tocontract,_addr,_nftids[i]);
        }
        g_Workedmap[nonce] == true;
        
    }

    ///1155<<<//////////////////////////////////////////////
    function onERC1155BatchReceived(
        address operator,
        address from,
        uint256[] calldata ids,
        uint256[] calldata values,
        bytes calldata data
    ) external pure returns (bytes4){
        return bytes4(keccak256("onERC1155BatchReceived(address,address,uint256[],uint256[],bytes)"));
    }

    function DoCross1155_CM(address _fromcontract,address _tocontract,uint256 _toChainId,address _fromaddr,address _toaddr,uint256[] memory _ids,uint256[] memory _values) payable external{
        require(_fromcontract != address(0)                     ,'p1');
        require(_tocontract != address(0)                       ,'p2');
        require(_toChainId != 0                                 ,'p3');
        //require(_fromaddr != address(0)                         ,'p4');
        require(_toaddr != address(0)                           ,'p5');
        require(msg.value > 0                                   ,'no fee');
        require(msg.sender == _fromaddr                         ,'p4');
        require(_ids.length <= 30                               ,'>30');
        
        g_FeeAddr.transfer(msg.value);

        require(g_CrossEx.DoCross1155_CM(msg.sender,_fromcontract,_fromaddr,_ids,_values) == true);

        // require(ERC1155(_fromcontract).isApprovedForAll(_fromaddr,address(this))==true,'isApprovedForAll err');
        // for(uint256 i = 0 ; i < _ids.length ; i++) {
        //     require(ERC1155(_fromcontract).balanceOf(_fromaddr,_ids[i]) >= _values[i],'balanceOf err');
        // }
        
        ERC1155(_fromcontract).safeBatchTransferFrom(_fromaddr,address(this),_ids,_values,hex"");
        event_CrossErc1155_CM(msg.value,_fromcontract,_tocontract,_toChainId,_fromaddr,_toaddr,_ids,_values);
        
        return;
    }
    //function WithdrawErc1155(bytes32 nonce,stmagic memory m,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256[] memory _ids,uint256[] memory _values,address _groupId,bytes calldata signs) external
    function WithdrawErc1155_CM(bytes32 nonce,stmagic memory m,st1155withdraw memory w,uint256[] memory _ids,uint256[] memory _values,address _groupId,bytes calldata signs) external
    {
        require(g_Workedmap[nonce] == false                     ,'p1');
        require(w.fromcontract != address(0)                    ,'p2');
        require(w.tocontract != address(0)                      ,'p3');
        require(w.addr != address(0)                            ,'p4');
        require(_groupId != address(0)                          ,'p6');
        require(signs.length == 65                              ,'p7');
        uint chainId;
        assembly {
            chainId := chainid()
        }
        require(chainId==w.fromchainId                          ,'p5');
        require(g_EventConfigContract.IsValidEvent(g_BusiName,m.fromchainid,m.frombridgecontract,m.eventname)==true,'IsValidEvent err');

        require(g_CrossEx.WithdrawErc1155_CM(nonce,m,w,_ids,_values,_groupId,signs) == true);

        // require(g_CrossEx.VerifyCrossErc1155Sign(nonce,m.fromchainid,m.frombridgecontract,m.eventname,w,_ids,_values,_groupId,signs) == true,'verify failed');
        // for(uint256 i = 0 ; i < _ids.length; i++){
        //     require(ERC1155(w.fromcontract).balanceOf(address(this),_ids[i]) >= _values[i],'balanceOf err');
        // }
        
        //ERC1155(w.fromcontract).setApprovalForAll(w.addr,true);
        ERC1155(w.fromcontract).safeBatchTransferFrom(address(this),w.addr,_ids,_values,hex"");
        //ERC1155(w.fromcontract).setApprovalForAll(w.addr,false);
        emit event_withdrawErc1155_CM(w.fromcontract,w.fromchainId,w.tocontract,w.addr,_ids,_values);
        
        g_Workedmap[nonce] == true;
        
    }
    ///1155>>>//////////////////////////////////////////////

    //////////////////////////////////////////////////////////////////////////////
    //event Event_ChangeSetter(address addr);
    //event Event_ChangeFeeAddr(address addr);
    //event Event_ChangeMutisign(address addr);
    //event Event_ChangeMutisign_CM(address addr);
    //event Event_ChangeBusiName(string name);
    event Event_SetEventCfg(address addr);
    event Event_SetCrossEx(address addr);

    // function ChangeSetter(address _addr) external {
    //     require(_addr != address(0)     ,'p1');
    //     require(msg.sender == g_Setter  ,'p2');

    //     g_Setter = _addr;
    //     emit Event_ChangeSetter(_addr);
    // }

    // function ChangeFeeAddr(address payable _addr) external {
    //     require(_addr != address(0)     ,'p1');
    //     require(msg.sender == g_Setter  ,'p2');

    //     g_FeeAddr = _addr;
    //     emit Event_ChangeFeeAddr(_addr);
    // }

    // function ChangeMutisign(address payable _addr) external {
    //     require(_addr != address(0)     ,'ChangeMutisign para err');
    //     require(msg.sender == g_Setter  ,'ChangeMutisign only can call by setter');

    //     g_MutiSignContract = (MutiSign)(_addr);
    //     emit Event_ChangeMutisign(_addr);
    // }
    
    // function ChangeMutisign_CM(address payable _addr) external {
    //     require(_addr != address(0)     ,'ChangeMutisign para err');
    //     require(msg.sender == g_Setter  ,'ChangeMutisign only can call by setter');

    //     g_MutiSignContract_CM = (MutiSign_CM)(_addr);
    //     emit Event_ChangeMutisign_CM(_addr);
    // }

    // function SetRPG(address _addr) external {
    //     require(_addr != address(0)     ,'SetRPG para err');
    //     require(msg.sender == g_Setter  ,'SetRPG only can call by setter');

    //     g_RPG = _addr;
    // }

    // function SetBusiName(string memory name) external {
    //     require(bytes(name).length > 0  ,'SetBusiName name err');
    //     require(msg.sender == g_Setter  ,'SetBusiName only can call by setter');

    //     g_BusiName = name;
    //     emit Event_ChangeBusiName(name);
    // }

    function SetEventCfg(address payable _addr) external {
        require(_addr != address(0)     ,'p1');
        require(msg.sender == g_Setter  ,'p2');

        g_EventConfigContract = EventConfig(_addr);
        emit Event_SetEventCfg(_addr);
    }

    function SetCrossEx(address _addr) external {
        require(_addr != address(0)     ,'p1');
        require(msg.sender == g_Setter  ,'p2');

        g_CrossEx = CrossContractEx(_addr);
        emit Event_SetCrossEx(_addr);
    }
    
}

struct stmagic {
    string fromchainid;
    string frombridgecontract;
    string eventname;
}

struct st1155withdraw {
    address fromcontract;
    uint256 fromchainId;
    address tocontract;
    address payable addr;
}

contract CrossContractEx is Ownable{
    address     public g_Parent;
    MutiSign_CM public g_MutiSignContract_CM;

    event Event_ChangeMutisign_CM(address addr);

    function init(address owner,address parent,address ms_cm) external{
        require(owner != address(0) ,'owner err');
        require(parent != address(0),'parent err');
        require(ms_cm != address(0) ,'ms_cm err');

        initOwner(owner);
        g_Parent = parent;
        g_MutiSignContract_CM = MutiSign_CM(ms_cm);
    }

    function ChangeMutisign_CM(address payable _addr) external onlyOwner{
        require(_addr != address(0)     ,'ChangeMutisign para err');

        g_MutiSignContract_CM = (MutiSign_CM)(_addr);
        emit Event_ChangeMutisign_CM(_addr);
    }

    function TryownerOf(address _fromcontract,uint256 _nftid,address owneraddr) view external returns(bool){
        require(msg.sender == g_Parent,'err sender');

        if(IERC721(_fromcontract).ownerOf(_nftid) == owneraddr){
            return true;
        }
        return false;
    }

    function verifymsg(bytes32 hashmsg,bytes memory signs,address groupId) private view returns(bool){
        (bool result,bool alive) = g_MutiSignContract_CM.CheckWitness(hashmsg,signs,groupId);
        return (result == true && alive == true);
    }

    function FormatDecimal(uint256 amount,uint256 dec,uint256 targetdec) view external returns(uint256){
        require(msg.sender == g_Parent,'err sender');

        uint256 am = amount;
        if(dec < targetdec){
            for(uint256 i = dec ; i < targetdec; i++ ){
                am = am*10;
            }
        }else if(dec > targetdec){
            for(uint256 i = targetdec ; i < dec; i++ ){
                am = am/10;
            }
        }
        return am;
    }

    function VerifyCrossErc20Sign(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _amount,address _groupId,bytes calldata _signs) external view returns(bool){
        require(msg.sender == g_Parent,'err sender');

        bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
        bytes32 magic = keccak256(str);

        str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_amount,_groupId,magic);
        bytes32 hashmsg = keccak256(str);

        if(verifymsg(hashmsg,_signs,_groupId) == false){
            return false;
        }
        return true;
    }

    function VerifyCrossErc20Sign2(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,bytes memory _tocontract,address payable _addr,uint256 _amount,address _groupId,bytes calldata _signs) external view returns(bool){
        require(msg.sender == g_Parent,'err sender');

        bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
        bytes32 magic = keccak256(str);

        str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_amount,_groupId,magic);
        bytes32 hashmsg = keccak256(str);

        if(verifymsg(hashmsg,_signs,_groupId) == false){
            return false;
        }
        return true;
    }

    // function VerifyCrossErc721Sign(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256 _nftid,address _groupId,bytes calldata signs) external view returns(bool){
    //     require(msg.sender == g_Parent,'err sender');

    //     bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
    //     bytes32 magic = keccak256(str);

    //     str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_nftid,_groupId,magic);
    //     bytes32 hashmsg = keccak256(str);

    //     if(verifymsg(hashmsg,signs,_groupId) == false){
    //         return false;
    //     }
    //     return true;
    // }

    function VerifyCrossErc721Sign_batch(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,address _fromcontract,uint256 _fromchainId,address _tocontract,address payable _addr,uint256[] memory _nftids,address _groupId,bytes calldata signs) external view returns(bool){
        require(msg.sender == g_Parent,'err sender');
        
        bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
        bytes32 magic = keccak256(str);

        str = abi.encodePacked(nonce,_fromcontract,_fromchainId,_tocontract,_addr,_nftids,_groupId,magic);
        bytes32 hashmsg = keccak256(str);

        if(verifymsg(hashmsg,signs,_groupId) == false){
            return false;
        }
        return true;
    }

    function VerifyCrossErc1155Sign(bytes32 nonce,string memory fromchainid,string memory frombridgecontract,string memory eventname,st1155withdraw memory w,uint256[] memory _ids,uint256[] memory _values,address _groupId,bytes calldata signs) private view returns(bool){
        require(msg.sender == g_Parent,'err sender');
        
        bytes memory str = abi.encodePacked(fromchainid,frombridgecontract,eventname);
        bytes32 magic = keccak256(str);

        str = abi.encodePacked(nonce,w.fromcontract,w.fromchainId,w.tocontract,w.addr,_ids,_values,_groupId,magic);
        bytes32 hashmsg = keccak256(str);

        if(verifymsg(hashmsg,signs,_groupId) == false){
            return false;
        }
        return true;
    }

    function DoCross1155_CM(address sender,address _fromcontract,address _fromaddr,uint256[] memory _ids,uint256[] memory _values) payable external returns(bool){
        require(msg.sender == g_Parent,'err sender');

        for(uint256 i = 0 ; i < _ids.length ; i++) {
            require(ERC1155(_fromcontract).balanceOf(_fromaddr,_ids[i]) >= _values[i],'balanceOf err');
        }
        if(sender == _fromaddr){
            return true;
        }
        require(ERC1155(_fromcontract).isApprovedForAll(_fromaddr,msg.sender)==true,'isApprovedForAll err');

        return true;
    }
    function WithdrawErc1155_CM(bytes32 nonce,stmagic memory m,st1155withdraw memory w,uint256[] memory _ids,uint256[] memory _values,address _groupId,bytes calldata signs) view external returns(bool){
        require(msg.sender == g_Parent,'err sender');

        require(VerifyCrossErc1155Sign(nonce,m.fromchainid,m.frombridgecontract,m.eventname,w,_ids,_values,_groupId,signs) == true,'verify failed');
        for(uint256 i = 0 ; i < _ids.length; i++){
            require(ERC1155(w.fromcontract).balanceOf(msg.sender,_ids[i]) >= _values[i],'balanceOf err');
        }
        return true;
    }
}

