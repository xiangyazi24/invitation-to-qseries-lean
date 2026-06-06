import QseriesFormalization.Chapter01_PartitionCount24
import QseriesFormalization.Chapter01_PartitionCount49

/-!
# Watson's strengthening of Ramanujan: `25 ∣ p(25n + 24)`

Chan §17 (and Watson 1938) strengthen Ramanujan's `5 ∣ p(5n+4)` to
`25 ∣ p(25n + 24)`.  The proof in Chan uses a series of η-quotient
identities.

Here we verify the small `n` cases by direct computation, using the
existing partition-count values in Chapter01_PartitionCount*.

The general theorem (∀n) is genuinely Watson-level work and not yet
formalized.
-/

namespace QseriesFormalization
namespace Pending
namespace Watson

open QseriesFormalization.Ch01 (partitionCount)

/-- `p(24) = 1575 = 25 · 63`. -/
theorem twentyfive_dvd_partition_twentyfour :
    25 ∣ partitionCount 24 := by
  rw [QseriesFormalization.Ch01.partitionCount_twentyfour]
  decide

/-- `p(49) = 173525 = 25 · 6941`. -/
theorem twentyfive_dvd_partition_fortynine :
    25 ∣ partitionCount 49 := by
  rw [QseriesFormalization.Ch01.partitionCount_fortynine]
  decide

end Watson
end Pending
end QseriesFormalization
