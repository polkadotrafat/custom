#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::traits::Get;
use frame_system::{
	self as system,
	offchain::{
		AppCrypto, CreateSignedTransaction, SendSignedTransaction, SendUnsignedTransaction,
		SignedPayload, Signer, SigningTypes, SubmitTransaction,
	},
};
use lite_json::json::JsonValue;
use sp_core::crypto::KeyTypeId;
use sp_runtime::{
	offchain::{
		http,
		storage::{MutateStorageError, StorageRetrievalError, StorageValueRef},
		Duration,
	},
	traits::Zero,
	transaction_validity::{InvalidTransaction, TransactionValidity, ValidTransaction},
	RuntimeDebug,
};
use sp_std::vec::Vec;
use hex;

pub const KEY_TYPE: KeyTypeId = KeyTypeId(*b"ocwd");
const HTTP_GRID_REMOTE_REQUEST: &str = "http://drex-env.eba-jkxuyqbq.us-east-1.elasticbeanstalk.com/grid/last";

/// Based on the above `KeyTypeId` we need to generate a pallet-specific crypto type wrappers.
/// We can use from supported crypto kinds (`sr25519`, `ed25519` and `ecdsa`) and augment
/// the types with this pallet-specific identifier.
pub mod crypto {
	use super::KEY_TYPE;
	use sp_core::sr25519::Signature as Sr25519Signature;
	use sp_runtime::{
		app_crypto::{app_crypto, sr25519},
		traits::Verify, MultiSignature, MultiSigner
	};
	app_crypto!(sr25519, KEY_TYPE);

	pub struct TestAuthId;

	// implemented for runtime
	impl frame_system::offchain::AppCrypto<MultiSigner, MultiSignature> for TestAuthId {
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}

	impl frame_system::offchain::AppCrypto<<Sr25519Signature as Verify>::Signer, Sr25519Signature>
		for TestAuthId
	{
		type RuntimeAppPublic = Public;
		type GenericSignature = sp_core::sr25519::Signature;
		type GenericPublic = sp_core::sr25519::Public;
	}
}

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// This pallet's configuration trait
	#[pallet::config]
	pub trait Config: CreateSignedTransaction<Call<Self>> + frame_system::Config {
		/// The identifier type for an offchain worker.
		type AuthorityId: AppCrypto<Self::Public, Self::Signature>;

		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The overarching dispatch call type.
		type Call: From<Call<Self>>;

		// Configuration parameters

		/// A grace period after we send transaction.
		///
		/// To avoid sending too many transactions, we only attempt to send one
		/// every `GRACE_PERIOD` blocks. We use Local Storage to coordinate
		/// sending between distinct runs of this offchain worker.
		#[pallet::constant]
		type GracePeriod: Get<Self::BlockNumber>;

		/// Number of blocks of cooldown after unsigned transaction is included.
		///
		/// This ensures that we only accept unsigned transactions once, every `UnsignedInterval`
		/// blocks.
		#[pallet::constant]
		type UnsignedInterval: Get<Self::BlockNumber>;

		/// A configuration for base priority of unsigned transactions.
		///
		/// This is exposed so that it can be tuned for particular runtime, when
		/// multiple pallets send unsigned transactions.
		#[pallet::constant]
		type UnsignedPriority: Get<TransactionPriority>;
	}

	#[pallet::pallet]
	#[pallet::without_storage_info]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Offchain Worker entry point.
		///
		/// By implementing `fn offchain_worker` you declare a new offchain worker.
		/// This function will be called when the node is fully synced and a new best block is
		/// succesfuly imported.
		/// Note that it's not guaranteed for offchain workers to run on EVERY block, there might
		/// be cases where some blocks are skipped, or for some the worker runs twice (re-orgs),
		/// so the code should be able to handle that.
		/// You can use `Local Storage` API to coordinate runs of the worker.
		fn offchain_worker(block_number: T::BlockNumber) {
			// Note that having logs compiled to WASM may cause the size of the blob to increase
			// significantly. You can use `RuntimeDebug` custom derive to hide details of the types
			// in WASM. The `sp-api` crate also provides a feature `disable-logging` to disable
			// all logging and thus, remove any logging from the WASM.
			log::info!("Hello from pallet-ocw.");

			// Since off-chain workers are just part of the runtime code, they have direct access
			// to the storage and other included pallets.
			//
			// We can easily import `frame_system` and retrieve a block hash of the parent block.
			let parent_hash = <system::Pallet<T>>::block_hash(block_number - 1u32.into());
			log::debug!("Current block: {:?} (parent hash: {:?})", block_number, parent_hash);

			// It's a good practice to keep `fn offchain_worker()` function minimal, and move most
			// of the code to separate `impl` block.
			// Here we call a helper function to calculate current average price.
			// This function reads storage entries of the current state.
			//let average: Option<u32> = Self::average_price();
			//log::debug!("Current price: {:?}", average);

			// For this example we are going to send both signed and unsigned transactions
			// depending on the block number.
			// Usually it's enough to choose one or the other.
			//let should_send = Self::choose_transaction_type(block_number);
			let res = Self::fetch_mini_grid_data();
			if let Err(e) = res {
				log::error!("Error: {}", e);
			}
		}
	}

	/// A public part of the pallet.
	#[pallet::call]
	impl<T: Config> Pallet<T> {

        #[pallet::weight(10000)]
		pub fn submit_mini_remote_block(origin: OriginFor<T>, address: Vec<u8>, energyacum: Vec<u8>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::set_remote_block(address.clone(),energyacum.clone());
			Ok(())
		}
	}

    #[pallet::storage]
	#[pallet::getter(fn devices)]
	pub(super) type Devices<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn remote_blocknumber)]
	pub(super) type RemoteBlock<T: Config> = StorageValue<_, u32, ValueQuery>;

	#[pallet::storage]
	#[pallet::getter(fn get_power_per_address)]
	pub(super) type TransactionsPerAddress<T:Config> = StorageMap<
		_,
		Blake2_128Concat,
		Vec<u8>,
		Vec<u8>,
		OptionQuery,
	>;

	/// Events for the pallet.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Event generated when new price is accepted to contribute to the average.
		/// \[price, who\]
		//NewPrice(u32, T::AccountId),
		DataFetched(u32),
	}


	/// Defines the block when next unsigned transaction will be accepted.
	///
	/// To prevent spam of unsigned (and unpayed!) transactions on the network,
	/// we only allow one transaction every `T::UnsignedInterval` blocks.
	/// This storage entry defines when new transaction is going to be accepted.
	#[pallet::storage]
	#[pallet::getter(fn next_unsigned_at)]
	pub(super) type NextUnsignedAt<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;
}


impl<T: Config> Pallet<T> {

    fn set_remote_block(address: Vec<u8>,power: Vec<u8>) {
		TransactionsPerAddress::<T>::insert(address,power);
    }

    fn fetch_mini_grid_data() -> Result<(), &'static str> {
		let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				"No local accounts available. Consider adding one via `author_insertKey` RPC.",
			)?
		}
		// Make an external HTTP request to fetch the current price.
		// Note this call will block until response is received.
		let result = Self::fetch_and_parse_data().map_err(|_| "Failed to fetch data")?;

		// Using `send_signed_transaction` associated type we create and submit a transaction
		// representing the call, we've just created.
		// Submit signed will return a vector of results for all accounts that were found in the
		// local keystore with expected `KEY_TYPE`.
		

		Ok(())
	}

    fn fetch_and_parse_data() -> Result<(), http::Error> {
		// We want to keep the offchain worker execution time reasonable, so we set a hard-coded
		// deadline to 2s to complete the external call.
		// You can also wait idefinitely for the response, however you may still get a timeout
		// coming from the host machine.
		let deadline = sp_io::offchain::timestamp().add(Duration::from_millis(2_000));
		// Initiate an external HTTP GET request.
		// This is using high-level wrappers from `sp_runtime`, for the low-level calls that
		// you can find in `sp_io`. The API is trying to be similar to `reqwest`, but
		// since we are running in a custom WASM execution environment we can't simply
		// import the library here.
		let request =
			http::Request::get(HTTP_GRID_REMOTE_REQUEST);

		// We set the deadline for sending of the request, note that awaiting response can
		// have a separate deadline. Next we send the request, before that it's also possible
		// to alter request headers or stream body content in case of non-GET requests.
		let pending = request.deadline(deadline).send().map_err(|_| http::Error::IoError)?;

		// The request is already being processed by the host, we are free to do anything
		// else in the worker (we can send multiple concurrent requests too).
		// At some point however we probably want to check the response though,
		// so we can block current thread and wait for it to finish.
		// Note that since the request is being driven by the host, we don't have to wait
		// for the request to have it complete, we will just not read the response.
		let response = pending.try_wait(deadline).map_err(|_| http::Error::DeadlineReached)??;
		// Let's check the status code before we proceed to reading the response.
		if response.code != 200 {
			log::warn!("Unexpected status code: {}", response.code);
			return Err(http::Error::Unknown)
		}

		// Next we want to fully read the response body and collect it to a vector of bytes.
		// Note that the return object allows you to read the body in chunks as well
		// with a way to control the deadline.
		let body = response.body().collect::<Vec<u8>>();

		// Create a str slice from the body.
		let body_str = sp_std::str::from_utf8(&body).map_err(|_| {
			log::warn!("No UTF8 body");
			http::Error::Unknown
		})?;

		log::info!("fetch_grid_data: {}", body_str);

        let signer = Signer::<T, T::AuthorityId>::all_accounts();
		if !signer.can_sign() {
			return Err(
				http::Error::Unknown
			)
		}

		let voltage = match Self::parse_voltage(body_str) {
			Some(voltage) => Ok(voltage),
			None => {
				log::warn!("Unable to extract energy from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got voltage: {:?} ", voltage);

		let current = match Self::parse_current(body_str) {
			Some(current) => Ok(current),
			None => {
				log::warn!("Unable to extract energy from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got current: {:?} ", current);

		let energy = match Self::parse_energy(body_str) {
			Some(energy) => Ok(energy),
			None => {
				log::warn!("Unable to extract energy from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got energy: {:?} ", energy);


        let gridcode = match Self::parse_gridcode(body_str) {
			Some(gridcode) => Ok(gridcode),
			None => {
				log::warn!("Unable to extract gridcode from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got gridcode: {:?} ", gridcode);

		let datetime = match Self::parse_datetime(body_str) {
			Some(datetime) => Ok(datetime),
			None => {
				log::warn!("Unable to extract datetime from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got datetime: {:?} ", datetime);

		let energyacum2 = match Self::parse_energyacum(body_str) {
			Some(energyacum2) => Ok(energyacum2),
			None => {
				log::warn!("Unable to extract energyacum from the response: {:?}", body_str);
				Err(http::Error::Unknown)
			},
		}?;

		log::info!("Got energyacum: {:?} ", energyacum2);

        let results = signer.send_signed_transaction(|_account| {
			// Received price is wrapped into a call to `submit_price` public function of this
			// pallet. This means that the transaction, when executed, will simply call that
			// function passing `price` as an argument.
			let address = gridcode.clone();
			let energyacum = energyacum2.clone();
			Call::submit_mini_remote_block { address,energyacum }
		});

		for (acc, res) in &results {
			match res {
				Ok(()) => log::info!("[{:?}] Submitted Transaction", acc.id),
				Err(e) => log::error!("[{:?}] Failed to submit transaction: {:?}", acc.id, e),
			}
		}


		Ok(())
	}

    fn parse_voltage(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let voltage = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("voltage".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = voltage.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}

	fn parse_current(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let current = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("current".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = current.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}

	fn parse_energy(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let energy = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("energy".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = energy.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}

    fn parse_gridcode(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let devices = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("grid-code".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = devices.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}

	fn parse_datetime(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let address = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("datetime".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = address.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}

	fn parse_energyacum(data_str: &str) -> Option<Vec<u8>> {
		let val = lite_json::parse_json(data_str);
		let power = match val.ok()? {
			JsonValue::Object(obj) => {
				let (_, v) = obj.into_iter().find(|(k, _)| k.iter().copied().eq("energy-acum".chars()))?;
				match v {
					JsonValue::String(value) => value,
					_ => return None,
				}
			},
			_ => return None,
		};

		let str_hex: Vec<u8> = power.iter().map(|c| *c as u8).collect::<Vec<_>>();
		log::info!("offchain_worker - str_hex {:?}", str_hex.clone());
		//let str2 = hex::decode(str_hex.clone()).ok()?;

		Some(str_hex)
	}
}