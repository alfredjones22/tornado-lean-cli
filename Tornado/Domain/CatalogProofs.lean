import Tornado.Domain.Catalog

namespace Tornado.Domain

/-- Finite catalog checks over the exact native constants used by the CLI. -/
theorem catalog_has_29_pools : allPools.length = 29 := by decide
theorem catalog_all_amounts_positive : allPools.all (fun pool => pool.amount > 0) = true := by decide
theorem catalog_mainnet_count : (poolsFor .mainnet).length = 20 := by decide
theorem catalog_sepolia_count : (poolsFor .sepolia).length = 9 := by decide
theorem catalog_address_unique : (allPools.map Pool.address).Nodup := by decide

end Tornado.Domain

#print axioms Tornado.Domain.catalog_has_29_pools
#print axioms Tornado.Domain.catalog_all_amounts_positive
#print axioms Tornado.Domain.catalog_mainnet_count
#print axioms Tornado.Domain.catalog_sepolia_count
#print axioms Tornado.Domain.catalog_address_unique
