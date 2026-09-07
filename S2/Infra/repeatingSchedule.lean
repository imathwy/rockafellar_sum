module

public import ReasLib.Data.Countable.RepeatingSchedule

public section

universe u

/- Infrastructure E.1 (Infinite repetition schedule for a countable type):
For every nonempty countable type, an explicit `ℕ`-indexed schedule has strictly increasing
occurrence subsequences. -/
#check (RepeatingSchedule.ofCountable :
  ∀ (α : Type u) [Countable α] [Nonempty α], RepeatingSchedule α)
