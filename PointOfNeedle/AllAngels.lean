import Mathlib

set_option linter.style.header false

/-!
# All possible angels: when is the number of dancing angels finite?

We do **not** assume the Thomistic doctrine that one angel occupies one place. Instead we
quantify over *every* angelic ontology we can formalise and classify when the number of
angels that can dance on a pin head is finite.

## Discrete pin (finitely many places `P`)

An `Ontology P` fixes
* `shapes` — the possible bodies ("footprints") of an angel: *any* finite family of sets of
  places. Mixed sizes model different choirs; `∅ ∈ shapes` models an immaterial angel.
* `mult` — how many angels may share one place (`1`: impenetrable, `c > 1`: partial
  compenetration).

Results:
* `count_le` — if no angel is immaterial, at most `mult * |P|` angels dance.
* `immaterial_canDance` — if immaterial angels exist, any number can dance.
* `bounded_iff` — **the number is finite iff no angel shape is empty.**
* `maxDancers`, `maxDancers_spec` — the finite maximum is computed by exhaustive search.
* `canDance_iff` — "can `k` angels dance?" is decidable for **every** ontology.

## Continuous pin (a set of finite measure)

* `card_mul_le_measure` — disjoint angels of size `≥ ε` number at most `μ(pin) / ε`.
* `bounded_of_size_ge` — hence a finite bound, whenever `ε > 0`.
* `bounded_of_finite_kinds` — finitely many kinds (e.g. the nine choirs) of positive size
  suffice for a finite bound.
* `countable_of_material` — material angels (positive size) are always at most countably many.
* `infinitely_many_shrinking` — but with positive sizes *without* a lower bound, infinitely
  many angels dance on `[0, 1]` at once: there is no finite answer.
* `point_angels_unbounded` — point-like (immaterial, size `0`) angels: unbounded.
-/

namespace PointOfNeedle.AllAngels

open Finset Function

section Discrete

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- An angelic ontology on a pin head whose places are `P`. -/
structure Ontology (P : Type*) where
  /-- The possible bodies of an angel. -/
  shapes : Finset (Finset P)
  /-- How many angels may share a single place. -/
  mult : ℕ

/-- A dance: how many angels take each possible body. -/
abbrev Dance (O : Ontology P) := O.shapes → ℕ

/-- How many angels cover place `p`. -/
def load (O : Ontology P) (d : Dance O) (p : P) : ℕ :=
  ∑ f : O.shapes, if p ∈ (f : Finset P) then d f else 0

/-- A dance is valid if no place is covered by more than `mult` angels. -/
def Valid (O : Ontology P) (d : Dance O) : Prop := ∀ p, load O d p ≤ O.mult

instance (O : Ontology P) (d : Dance O) : Decidable (Valid O d) := by
  unfold Valid; infer_instance

/-- The number of dancing angels. -/
def count (O : Ontology P) (d : Dance O) : ℕ := ∑ f, d f

/-- The ontology admits immaterial angels (occupying no place). -/
def Immaterial (O : Ontology P) : Prop := ∅ ∈ O.shapes

instance (O : Ontology P) : Decidable (Immaterial O) := by
  unfold Immaterial; infer_instance

/-- `k` angels can dance. -/
def CanDance (O : Ontology P) (k : ℕ) : Prop := ∃ d : Dance O, Valid O d ∧ count O d = k

variable (O : Ontology P)

lemma sum_load (d : Dance O) : ∑ p, load O d p = ∑ f : O.shapes, f.1.card * d f := by
  unfold load
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 2
  ext p; simp

/-- **Material angels are finitely many**: at most `mult * |P|`. -/
theorem count_le (hO : ¬ Immaterial O) {d : Dance O} (hd : Valid O d) :
    count O d ≤ O.mult * Fintype.card P := by
  calc count O d = ∑ f, d f := rfl
    _ ≤ ∑ f : O.shapes, (f : Finset P).card * d f := by
        refine Finset.sum_le_sum fun f _ => ?_
        have : 0 < (f : Finset P).card := by
          rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
          intro h
          have := f.2
          rw [h] at this
          exact hO this
        exact Nat.le_mul_of_pos_left _ this
    _ = ∑ p, load O d p := (sum_load O d).symm
    _ ≤ ∑ _p : P, O.mult := Finset.sum_le_sum fun p _ => hd p
    _ = O.mult * Fintype.card P := by simp [mul_comm]

omit [Fintype P] in
/-- In a valid material dance, each body is taken by at most `mult` angels. -/
lemma le_mult (hO : ¬ Immaterial O) {d : Dance O} (hd : Valid O d) (f : O.shapes) :
    d f ≤ O.mult := by
  obtain ⟨p, hp⟩ : (f : Finset P).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have := f.2
    rw [h] at this
    exact hO this
  refine le_trans ?_ (hd p)
  unfold load
  have := Finset.single_le_sum (f := fun g : O.shapes => if p ∈ (g : Finset P) then d g else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ f)
  simpa [hp] using this

omit [Fintype P] in
/-- **Immaterial angels are unboundedly many**: any number of them can dance. -/
theorem immaterial_canDance (hO : Immaterial O) (k : ℕ) : CanDance O k := by
  classical
  let e : O.shapes := ⟨∅, hO⟩
  refine ⟨fun f => if f = e then k else 0, fun p => ?_, ?_⟩
  · unfold load
    rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    · intro f _
      by_cases hf : f = e
      · subst hf; simp [e]
      · simp [hf]
  · simp [count]

omit [Fintype P] in
/-- **Classification**: the number of dancing angels is bounded iff no angel is immaterial. -/
theorem bounded_iff [Finite P] :
    (∃ M, ∀ d : Dance O, Valid O d → count O d ≤ M) ↔ ¬ Immaterial O := by
  constructor
  · rintro ⟨M, hM⟩ hO
    obtain ⟨d, hd, hc⟩ := immaterial_canDance O hO (M + 1)
    have := hM d hd
    omega
  · intro hO
    have := Fintype.ofFinite P
    exact ⟨_, fun d hd => count_le O hO hd⟩

/-- The maximal number of dancing angels, by exhaustive search over the finitely many
candidate dances (each body taken by at most `mult` angels). -/
def maxDancers : ℕ :=
  ((Fintype.piFinset fun _ : O.shapes => range (O.mult + 1)).filter (Valid O)).sup (count O)

lemma mem_search (hO : ¬ Immaterial O) {d : Dance O} (hd : Valid O d) :
    d ∈ (Fintype.piFinset fun _ : O.shapes => range (O.mult + 1)).filter (Valid O) := by
  simp only [mem_filter, Fintype.mem_piFinset, mem_range]
  exact ⟨fun f => Nat.lt_succ_of_le (le_mult O hO hd f), hd⟩

omit [Fintype P] in
lemma valid_zero : Valid O 0 := fun p => by simp [load]

/-- `maxDancers` is the true maximum for every material ontology. -/
theorem maxDancers_spec (hO : ¬ Immaterial O) :
    (∃ d, Valid O d ∧ count O d = maxDancers O) ∧
      ∀ d, Valid O d → count O d ≤ maxDancers O := by
  refine ⟨?_, fun d hd => Finset.le_sup (mem_search O hO hd)⟩
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup _ ⟨0, mem_search O hO (valid_zero O)⟩ (count O)
  exact ⟨d, (mem_filter.1 hd).2, heq.symm⟩

omit [Fintype P] in
/-- Removing one angel from a valid dance keeps it valid. -/
lemma canDance_pred {k : ℕ} (h : CanDance O (k + 1)) : CanDance O k := by
  classical
  obtain ⟨d, hd, hc⟩ := h
  obtain ⟨f, -, hf⟩ : ∃ f ∈ (univ : Finset O.shapes), d f ≠ 0 := by
    by_contra hne
    push Not at hne
    have : count O d = 0 := Finset.sum_eq_zero hne
    omega
  let d' : Dance O := Function.update d f (d f - 1)
  have hle : ∀ g, d' g ≤ d g := by
    intro g
    by_cases hg : g = f
    · subst hg; simp [d']
    · simp [d', hg]
  refine ⟨d', fun p => le_trans ?_ (hd p), ?_⟩
  · unfold load
    exact Finset.sum_le_sum fun g _ => by split_ifs <;> simp [hle g]
  · have h1 := Finset.sum_update_of_mem (Finset.mem_univ f) d (d f - 1)
    rw [Finset.sdiff_singleton_eq_erase] at h1
    have h2 := Finset.add_sum_erase (univ : Finset O.shapes) d (Finset.mem_univ f)
    simp only [count] at hc ⊢
    simp only [d']
    omega

omit [Fintype P] in
lemma canDance_of_le {m : ℕ} (h : CanDance O m) {k : ℕ} (hk : k ≤ m) : CanDance O k := by
  induction m with
  | zero => exact Nat.le_zero.1 hk ▸ h
  | succ m ih =>
    rcases Nat.lt_or_ge k (m + 1) with hlt | hge
    · exact ih (canDance_pred O h) (Nat.le_of_lt_succ hlt)
    · exact le_antisymm hk hge ▸ h

/-- **Decision procedure for every ontology**: `k` angels can dance iff the ontology admits
immaterial angels or `k` does not exceed the searched maximum. -/
theorem canDance_iff (k : ℕ) : CanDance O k ↔ Immaterial O ∨ k ≤ maxDancers O := by
  by_cases hO : Immaterial O
  · simp [hO, immaterial_canDance O hO k]
  · simp only [hO, false_or]
    obtain ⟨⟨d, hd, heq⟩, hle⟩ := maxDancers_spec O hO
    constructor
    · rintro ⟨e, he, rfl⟩; exact hle e he
    · intro hk; exact canDance_of_le O ⟨d, hd, heq⟩ hk

instance (k : ℕ) : Decidable (CanDance O k) :=
  decidable_of_iff _ (canDance_iff O k).symm

end Discrete

section Continuous

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

/-- Angels whose bodies are (almost) disjoint and of size at least `ε`: `card * ε ≤ μ(pin)`.
Bodies may touch along null sets (e.g. share a boundary). -/
theorem card_mul_le_measure {ι : Type*} (s : Finset ι) (A : ι → Set X) (pin : Set X)
    (hA : ∀ i ∈ s, NullMeasurableSet (A i) μ) (hsub : ∀ i ∈ s, A i ⊆ pin)
    (hdisj : (s : Set ι).Pairwise (AEDisjoint μ on A)) (ε : ℝ≥0∞)
    (hε : ∀ i ∈ s, ε ≤ μ (A i)) :
    s.card * ε ≤ μ pin := by
  calc (s.card : ℝ≥0∞) * ε = ∑ _i ∈ s, ε := by simp
    _ ≤ ∑ i ∈ s, μ (A i) := Finset.sum_le_sum hε
    _ = μ (⋃ i ∈ s, A i) := (measure_biUnion_finset₀ hdisj hA).symm
    _ ≤ μ pin := measure_mono (Set.iUnion₂_subset hsub)

/-- **Material angels with a minimum size are finitely many**, on a pin of finite area. -/
theorem bounded_of_size_ge (pin : Set X) (hpin : μ pin ≠ ∞) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ M : ℕ, ∀ {ι : Type*} (s : Finset ι) (A : ι → Set X),
      (∀ i ∈ s, NullMeasurableSet (A i) μ) → (∀ i ∈ s, A i ⊆ pin) →
      (s : Set ι).Pairwise (AEDisjoint μ on A) → (∀ i ∈ s, ε ≤ μ (A i)) → s.card ≤ M := by
  refine ⟨⌊(μ pin / ε).toReal⌋₊, fun s A hA hsub hdisj hsize => ?_⟩
  have h := card_mul_le_measure μ s A pin hA hsub hdisj ε hsize
  have h' : (s.card : ℝ≥0∞) ≤ μ pin / ε := ENNReal.le_div_iff_mul_le (Or.inl hε)
    (Or.inr hpin) |>.2 h
  have hfin : μ pin / ε ≠ ∞ := ENNReal.div_ne_top hpin hε
  apply Nat.le_floor
  have := ENNReal.toReal_mono hfin h'
  simpa using this

/-- **Finitely many kinds of angels** (e.g. the nine choirs), each kind of positive size:
still finitely many dancers. -/
theorem bounded_of_finite_kinds {K : Type*} [Finite K] (size : K → ℝ≥0∞)
    (hsize : ∀ k, 0 < size k) (pin : Set X) (hpin : μ pin ≠ ∞) :
    ∃ M : ℕ, ∀ {ι : Type*} (s : Finset ι) (A : ι → Set X) (kind : ι → K),
      (∀ i ∈ s, NullMeasurableSet (A i) μ) → (∀ i ∈ s, A i ⊆ pin) →
      (s : Set ι).Pairwise (AEDisjoint μ on A) → (∀ i ∈ s, size (kind i) ≤ μ (A i)) →
      s.card ≤ M := by
  have := Fintype.ofFinite K
  have hpos : 0 < (univ : Finset K).inf size :=
    (Finset.lt_inf_iff ENNReal.zero_lt_top).2 fun k _ => hsize k
  obtain ⟨M, hM⟩ := bounded_of_size_ge μ pin hpin _ hpos.ne'
  exact ⟨M, fun s A kind hA hsub hdisj hs =>
    hM s A hA hsub hdisj fun i hi => (Finset.inf_le (mem_univ _)).trans (hs i hi)⟩

/-- **Material angels are at most countably many**, however small, on a pin of finite area. -/
theorem countable_of_material {ι : Type*} (A : ι → Set X) (pin : Set X) (hpin : μ pin ≠ ∞)
    (hA : ∀ i, NullMeasurableSet (A i) μ) (hsub : ∀ i, A i ⊆ pin)
    (hdisj : Pairwise (Disjoint on A)) (hpos : ∀ i, 0 < μ (A i)) : Countable ι := by
  have hc := Measure.countable_meas_pos_of_disjoint_of_meas_iUnion_ne_top₀ μ hA
    (fun i j hij => (hdisj hij).aedisjoint)
    (ne_top_of_le_ne_top hpin (measure_mono (Set.iUnion_subset hsub)))
  have : {i | 0 < μ (A i)} = Set.univ := Set.eq_univ_of_forall hpos
  rw [this] at hc
  exact Set.countable_univ_iff.1 hc

/-- **Shrinking angels**: with positive sizes but no minimum, *infinitely many* angels dance on
`[0, 1]` at once — the `n`-th occupying `[1 - 2⁻ⁿ, 1 - 2⁻⁽ⁿ⁺¹⁾)`. No finite answer exists. -/
theorem infinitely_many_shrinking :
    ∃ A : ℕ → Set ℝ, (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ Set.Icc 0 1) ∧
      Pairwise (Disjoint on A) ∧ ∀ n, 0 < volume (A n) := by
  let f : ℕ → ℝ := fun n => 1 - (1 / 2 : ℝ) ^ n
  have hf : Monotone f := fun m n hmn => by
    have : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ m := pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
    simp only [f]; linarith
  refine ⟨fun n => Set.Ico (f n) (f (n + 1)), fun n => measurableSet_Ico, fun n => ?_,
    hf.pairwise_disjoint_on_Ico_succ, fun n => ?_⟩
  · intro x hx
    have h0 : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h1 : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
    simp only [Set.mem_Ico, f] at hx
    constructor <;> linarith [hx.1, hx.2]
  · rw [Real.volume_Ico, ENNReal.ofReal_pos]
    simp only [f, pow_succ]
    have : 0 < (1 / 2 : ℝ) ^ n := by positivity
    linarith

/-- Consequently, for shrinking angels, *every* finite number is exceeded. -/
theorem shrinking_unbounded (M : ℕ) :
    ∃ (s : Finset ℕ) (A : ℕ → Set ℝ), (∀ i ∈ s, MeasurableSet (A i)) ∧
      (∀ i ∈ s, A i ⊆ Set.Icc 0 1) ∧ (s : Set ℕ).Pairwise (Disjoint on A) ∧
      (∀ i ∈ s, 0 < volume (A i)) ∧ M < s.card := by
  obtain ⟨A, hm, hs, hd, hp⟩ := infinitely_many_shrinking
  exact ⟨range (M + 1), A, fun i _ => hm i, fun i _ => hs i, fun i _ j _ hij => hd hij,
    fun i _ => hp i, by simp⟩

/-- **Point-like angels** (distinct points, size zero) on `[0, 1]`: any number can dance. -/
theorem point_angels_unbounded (k : ℕ) :
    ∃ s : Finset ℝ, (↑s : Set ℝ) ⊆ Set.Icc 0 1 ∧ s.card = k :=
  (Set.Icc_infinite (zero_lt_one' ℝ)).exists_subset_card_eq k

end Continuous

/-! ### Examples, evaluated by exhaustive search -/

section Examples

/-- A pin with 4 places; angels are either single places or adjacent pairs. -/
def smallAngels (mult : ℕ) : Ontology (Fin 4) :=
  ⟨{{0}, {1}, {2}, {3}, {0, 1}, {1, 2}, {2, 3}}, mult⟩

/-- Only "large" angels (adjacent pairs) — a different choir. -/
def largeAngels : Ontology (Fin 4) := ⟨{{0, 1}, {1, 2}, {2, 3}}, 1⟩

/-- info: 4 -/
#guard_msgs in
#eval maxDancers (smallAngels 1)

/-- info: 8 -/
#guard_msgs in
#eval maxDancers (smallAngels 2)

/-- info: 2 -/
#guard_msgs in
#eval maxDancers largeAngels

example : CanDance largeAngels 2 ∧ ¬ CanDance largeAngels 3 := by decide

/-- With an immaterial angel admitted, a thousand angels dance on four places. -/
example : CanDance (⟨{∅, {0}}, 1⟩ : Ontology (Fin 4)) 1000 := by decide

end Examples

end PointOfNeedle.AllAngels
