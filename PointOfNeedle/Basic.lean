import Mathlib

set_option linter.style.header false

/-!
# How many angels can dance on the head of a pin?

We formalise the scholastic question and prove that, under any reasonable
*finite, decidable* model, the answer is **computable**.

* `capacity pin close` — for a finite set `pin` of places and a decidable relation
  `close a b` ("`a` and `b` are too close for two angels to dance there"), the maximum
  number of angels that fit. It is defined by exhaustive search, hence is an honest
  (non-`noncomputable`) Lean function.
  - `card_le_capacity`, `exists_eq_capacity`: it really is the maximum.
  - `canDance_iff`: "can `k` angels dance?" holds iff `k ≤ capacity`, so it is decidable
    (`instance : Decidable (CanDance pin close k)`).

* The concrete model: the pin head is an `n × n` grid of Planck cells, and a dancing
  angel needs the eight surrounding cells free (`tooClose` = king-adjacent or equal).
  - `danceCapacity_eq`: the brute-force answer equals `((n + 1) / 2) ^ 2`, i.e. `⌈n/2⌉²`.
  - `danceCapacity_primrec`, `danceCapacity_computable`: the answer is primitive recursive,
    in particular computable in the sense of Mathlib's `Computable`.

* The Thomistic model (Summa Theologiae I, q. 52, a. 3: two angels cannot be in the same
  place): `thomisticCapacity_eq : capacity (pinHead n) (· = ·) = n ^ 2`, also computable.

* Angels that may freely overlap: no finite bound exists (`overlapping_unbounded`), yet the
  question "can `k` angels dance?" is still (trivially) decidable.
-/

namespace PointOfNeedle

open Finset

section General

variable {α : Type*} [DecidableEq α]

/-- A configuration `s` of angels is admissible if no two distinct angels are too close. -/
def Admissible (close : α → α → Prop) (s : Finset α) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ¬ close a b

instance (close : α → α → Prop) [DecidableRel close] (s : Finset α) :
    Decidable (Admissible close s) := by
  unfold Admissible; infer_instance

omit [DecidableEq α] in
lemma admissible_empty (close : α → α → Prop) : Admissible close (∅ : Finset α) := by
  simp [Admissible]

omit [DecidableEq α] in
lemma Admissible.mono {close : α → α → Prop} {s t : Finset α} (h : Admissible close s)
    (hts : t ⊆ s) : Admissible close t :=
  fun a ha b hb hab => h a (hts ha) b (hts hb) hab

/-- The maximum number of angels that can dance on `pin`, found by exhaustive search. -/
def capacity (pin : Finset α) (close : α → α → Prop) [DecidableRel close] : ℕ :=
  (pin.powerset.filter (Admissible close)).sup Finset.card

/-- `k` angels can dance on `pin`. -/
def CanDance (pin : Finset α) (close : α → α → Prop) (k : ℕ) : Prop :=
  ∃ s ⊆ pin, Admissible close s ∧ s.card = k

variable (pin : Finset α) (close : α → α → Prop) [DecidableRel close]

/-- No admissible configuration exceeds `capacity`. -/
theorem card_le_capacity {s : Finset α} (hs : s ⊆ pin) (h : Admissible close s) :
    s.card ≤ capacity pin close :=
  Finset.le_sup (f := Finset.card) (by simp [hs, h])

/-- `capacity` is attained. -/
theorem exists_eq_capacity :
    ∃ s ⊆ pin, Admissible close s ∧ s.card = capacity pin close := by
  obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_sup (pin.powerset.filter (Admissible close))
    ⟨∅, by simp [admissible_empty]⟩ Finset.card
  simp only [mem_filter, mem_powerset] at hs
  exact ⟨s, hs.1, hs.2, heq.symm⟩

/-- Characterisation of `capacity` as *the* maximum. -/
theorem capacity_eq_iff (m : ℕ) :
    capacity pin close = m ↔
      (∃ s ⊆ pin, Admissible close s ∧ s.card = m) ∧
      ∀ s ⊆ pin, Admissible close s → s.card ≤ m := by
  constructor
  · rintro rfl
    exact ⟨exists_eq_capacity pin close, fun s hs h => card_le_capacity pin close hs h⟩
  · rintro ⟨⟨s, hs, h, rfl⟩, hle⟩
    obtain ⟨t, ht, ht', heq⟩ := exists_eq_capacity pin close
    exact le_antisymm (heq ▸ hle t ht ht') (card_le_capacity pin close hs h)

/-- `k` angels can dance iff `k` does not exceed the capacity. -/
theorem canDance_iff (k : ℕ) : CanDance pin close k ↔ k ≤ capacity pin close := by
  constructor
  · rintro ⟨s, hs, h, rfl⟩
    exact card_le_capacity pin close hs h
  · intro hk
    obtain ⟨s, hs, h, heq⟩ := exists_eq_capacity pin close
    obtain ⟨t, hts, rfl⟩ := Finset.exists_subset_card_eq (heq ▸ hk : k ≤ s.card)
    exact ⟨t, hts.trans hs, h.mono hts, rfl⟩

/-- Whether `k` angels can dance on a pin is decidable. -/
instance (k : ℕ) : Decidable (CanDance pin close k) :=
  decidable_of_iff _ (canDance_iff pin close k).symm

end General

section Grid

/-- The head of a pin: an `n × n` grid of Planck cells. -/
def pinHead (n : ℕ) : Finset (ℕ × ℕ) := range n ×ˢ range n

/-- Two dancing angels are too close if they are in the same or in adjacent cells
(horizontally, vertically or diagonally): each needs room to spread its wings. -/
def tooClose (p q : ℕ × ℕ) : Prop :=
  p.1 ≤ q.1 + 1 ∧ q.1 ≤ p.1 + 1 ∧ p.2 ≤ q.2 + 1 ∧ q.2 ≤ p.2 + 1

instance : DecidableRel tooClose := fun _ _ => by unfold tooClose; infer_instance

/-- The number of angels that can dance on an `n × n` pin head, by exhaustive search. -/
def danceCapacity (n : ℕ) : ℕ := capacity (pinHead n) tooClose

/-- The closed form `⌈n/2⌉²`. -/
def danceFormula (n : ℕ) : ℕ := (n + 1) / 2 * ((n + 1) / 2)

/-- The explicit choreography: angels at every cell with even coordinates. -/
def choreography (n : ℕ) : Finset (ℕ × ℕ) :=
  (range ((n + 1) / 2) ×ˢ range ((n + 1) / 2)).image fun p => (2 * p.1, 2 * p.2)

lemma choreography_subset (n : ℕ) : choreography n ⊆ pinHead n := by
  intro q hq
  simp only [choreography, mem_image, mem_product, mem_range] at hq
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ := hq
  simp only [pinHead, mem_product, mem_range]
  omega

lemma choreography_admissible (n : ℕ) : Admissible tooClose (choreography n) := by
  intro p hp q hq hpq hclose
  simp only [choreography, mem_image] at hp hq
  obtain ⟨⟨a, b⟩, -, rfl⟩ := hp
  obtain ⟨⟨c, d⟩, -, rfl⟩ := hq
  simp only [tooClose] at hclose
  apply hpq
  ext <;> simp <;> omega

lemma choreography_card (n : ℕ) : (choreography n).card = danceFormula n := by
  rw [choreography, card_image_of_injective, card_product, card_range, danceFormula]
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [Prod.mk.injEq] at h
  ext <;> simp <;> omega

/-- Upper bound: two angels never share a `2 × 2` block, and there are `⌈n/2⌉²` blocks. -/
lemma card_le_danceFormula {n : ℕ} {s : Finset (ℕ × ℕ)} (hs : s ⊆ pinHead n)
    (h : Admissible tooClose s) : s.card ≤ danceFormula n := by
  have key : s.card ≤ (range ((n + 1) / 2) ×ˢ range ((n + 1) / 2)).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.1 / 2, p.2 / 2))
    · intro p hp
      have := hs hp
      simp only [pinHead, mem_product, mem_range] at this
      simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio]
      omega
    · intro p hp q hq hpq
      by_contra hne
      apply h p hp q hq hne
      simp only [Prod.mk.injEq] at hpq
      simp only [tooClose]
      omega
  simpa [danceFormula] using key

/-- **Main theorem.** The exhaustive-search answer equals `⌈n/2⌉²`. -/
theorem danceCapacity_eq (n : ℕ) : danceCapacity n = danceFormula n :=
  (capacity_eq_iff _ _ _).2
    ⟨⟨choreography n, choreography_subset n, choreography_admissible n, choreography_card n⟩,
      fun _ hs h => card_le_danceFormula hs h⟩

theorem danceFormula_primrec : Primrec danceFormula := by
  have h : Primrec fun n : ℕ => (n + 1) / 2 :=
    Primrec.nat_div.comp Primrec.succ (Primrec.const 2)
  exact Primrec.nat_mul.comp h h

/-- **The number of angels that can dance on the head of a pin is primitive recursive.** -/
theorem danceCapacity_primrec : Primrec danceCapacity := by
  have : danceCapacity = danceFormula := funext danceCapacity_eq
  rw [this]
  exact danceFormula_primrec

/-- **The number of angels that can dance on the head of a pin is computable.** -/
theorem danceCapacity_computable : Computable danceCapacity :=
  danceCapacity_primrec.to_comp

/-- Whether `k` angels can dance on an `n × n` pin head is a primitive recursive
(hence decidable) predicate of `(n, k)`. -/
theorem canDance_primrecPred :
    PrimrecPred fun nk : ℕ × ℕ => CanDance (pinHead nk.1) tooClose nk.2 := by
  have : (fun nk : ℕ × ℕ => CanDance (pinHead nk.1) tooClose nk.2) =
      fun nk => nk.2 ≤ danceFormula nk.1 := by
    funext nk
    rw [canDance_iff, ← danceCapacity_eq]
    rfl
  rw [this]
  exact Primrec.nat_le.comp Primrec.snd (danceFormula_primrec.comp Primrec.fst)

end Grid

section Thomistic

/-- Aquinas: two angels are never in the same place at once, but nothing more is required. -/
theorem thomisticCapacity_eq (n : ℕ) : capacity (pinHead n) (· = ·) = n ^ 2 := by
  rw [capacity_eq_iff]
  refine ⟨⟨pinHead n, subset_rfl, fun _ _ _ _ h => h, by simp [pinHead, sq]⟩, ?_⟩
  intro s hs _
  simpa [pinHead, sq] using card_le_card hs

theorem thomisticCapacity_computable :
    Computable fun n => capacity (pinHead n) (· = ·) := by
  have : (fun n => capacity (pinHead n) (· = ·)) = fun n => n * n := by
    funext n; rw [thomisticCapacity_eq, sq]
  rw [this]
  exact (Primrec.nat_mul.comp Primrec.id Primrec.id).to_comp

end Thomistic

section Overlapping

/-- If angels are allowed to overlap arbitrarily (configurations are multisets of cells with
no exclusion), there is no finite answer as soon as the pin has a place at all… -/
theorem overlapping_unbounded (n : ℕ) :
    ¬ ∃ M : ℕ, ∀ m : Multiset (ℕ × ℕ), (∀ p ∈ m, p ∈ pinHead (n + 1)) → m.card ≤ M := by
  rintro ⟨M, hM⟩
  have := hM (Multiset.replicate (M + 1) (0, 0)) (by
    intro p hp
    rw [Multiset.eq_of_mem_replicate hp]
    simp [pinHead])
  simp at this

/-- …but the question "can `k` angels dance?" remains (trivially) decidable: always yes. -/
theorem overlapping_canDance (n k : ℕ) :
    ∃ m : Multiset (ℕ × ℕ), (∀ p ∈ m, p ∈ pinHead (n + 1)) ∧ m.card = k :=
  ⟨Multiset.replicate k (0, 0), fun p hp => by
    rw [Multiset.eq_of_mem_replicate hp]; simp [pinHead], by simp⟩

end Overlapping

/-! ### Actually computing it -/

-- Exhaustive search, run by the Lean kernel's evaluator (2^16 configurations for `n = 4`).
/-- info: 4 -/
#guard_msgs in
#eval danceCapacity 4

/-- A pin head about 1 mm across is roughly `6.2 × 10^31` Planck lengths wide. -/
def realisticPin : ℕ := 62 * 10 ^ 30

/-- …so about `9.6 × 10^62` angels can dance on it. -/
example : danceCapacity realisticPin = 961 * 10 ^ 60 := by
  rw [danceCapacity_eq]; decide +kernel

end PointOfNeedle
