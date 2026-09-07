/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Data.Countable.RepeatingSchedule

/-!
# Repeating schedules

This source-facing module records the canonical repeating schedule on a
nonempty countable type.
-/

public section

universe u

/- Infrastructure E.1 (Infinite repetition schedule for a countable type):
For every nonempty countable type, an explicit `ℕ`-indexed schedule has strictly increasing
occurrence subsequences. -/
#check (RepeatingSchedule.ofCountable :
  ∀ (α : Type u) [Countable α] [Nonempty α], RepeatingSchedule α)
