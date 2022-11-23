#![cfg_attr(not(feature = "std"), no_std)]

use cumulus_pallet_xcm::{ensure_sibling_para, Origin as CumulusOrigin};
use cumulus_primitives_core::ParaId;
use frame_system::Config as SystemConfig;
use sp_std::prelude::*;
use xcm::latest::prelude::*;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
    use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::type_value]
    pub fn MintBaseline<T: Config>() -> u32
    {
        1000u32
    }


    #[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

    #[pallet::config]
	pub trait Config: frame_system::Config +pallet_ocw::Config{
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		type Origin: From<<Self as SystemConfig>::Origin>
			+ Into<Result<CumulusOrigin, <Self as Config>::Origin>>;

		/// The overarching call type; we assume sibling chains use the same type.
		type Call: From<Call<Self>> + Encode;

		type XcmSender: SendXcm;
	}

    #[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		DataFetched(u32),
	}

	#[pallet::error]
	pub enum Error<T> {
		DataMissing,		
	}

    #[pallet::storage]
	#[pallet::getter(fn get_previous_power)]
	pub(super) type PrevTransactions<T:Config> = StorageMap<
		_,
		Blake2_128Concat,
		Vec<u8>,
		u32,
		OptionQuery,
	>;


	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(10_000)]
		pub fn check_data(who: OriginFor<T>, id: Vec<u8>) -> DispatchResult {
			//let current_val: u32 = pallet_ocw::Pallet::<T>::get_power_per_address(id.clone()).unwrap();
			//let prev_val: u32 = Self::get_previous_power(id.clone()).unwrap();
			//let diff: u32 = current_val - prev_val;
			//let num: u32 = Self::get_num_of_tokens(diff.clone());
			//let incr: u32 = num * 1000u32;
			//Self::mint_token(num);
			//PrevTransactions::<T>::insert(id.clone(),incr);

			Ok(())
		}

	}

	// Helpful functions
	impl<T: Config> Pallet<T> {
		pub fn mint_token(num: u32) {

		}

		pub fn get_num_of_tokens(diff: u32) -> u32 {
			let num: u32 = diff.saturating_div(1000u32);
			num
		}
	}
}