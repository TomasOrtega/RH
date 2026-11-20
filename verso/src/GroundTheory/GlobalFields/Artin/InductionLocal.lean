import Mathlib
import GroundTheory.GlobalFields.Artin.InductionFrobenius
import GroundTheory.GlobalFields.Artin.Series
import GroundTheory.GlobalFields.Artin.InflationTower
set_option maxSynthPendingDepth 1

noncomputable section

open scoped Pointwise
open NumberField IsDedekindDomain IntermediateField GroundTheory.LocalField

namespace GroundTheory.Global.Artin

section Transfer

variable {G Γ : Type*} [Group G] [Group Γ]

/- English proof (translation)
Rewrite using `[cosetAverage_eq_sum, cosetAvg, zpow_natCast]`.
-/
theorem cosetAverage_pow_eq_cosetAvg (J : Subgroup G) [Fintype J] (a : G) (F : G → ℂ) (k : ℕ) :
    cosetAverage J F (a ^ k) = cosetAvg J a F k := by
  rw [cosetAverage_eq_sum, cosetAvg, zpow_natCast]

/- English proof (translation)
Establish `h` using `cosetAverage_comp J e.toMonoidHom (F ∘ e.symm) g`. Establish `h2 : (F ∘ e.symm) ∘ e.toMonoidHom = F` using `funext fun x ↦ by simp`. Rewrite `h` using `[h2]`. Conclude with `h.symm`.
-/
theorem cosetAverage_map_mulEquiv (e : G ≃* Γ) (J : Subgroup G) [Finite J] (F : G → ℂ) (g : G) :
    cosetAverage (J.map e.toMonoidHom) (F ∘ e.symm) (e g) = cosetAverage J F g := by
  have h := cosetAverage_comp J e.toMonoidHom (F ∘ e.symm) g
  have h2 : (F ∘ e.symm) ∘ e.toMonoidHom = F := funext fun x ↦ by simp
  rw [h2] at h
  exact h.symm

end Transfer

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] (H : Subgroup Gal(L/K))

def fixedFieldFun (f : H → ℂ) : Gal(L/fixedField H) → ℂ :=
  f ∘ (fixedFieldMulEquiv H).symm

omit [IsGalois K L] in
@[simp]
/- English proof (translation)
Simplify using `[fixedFieldFun]`.
-/
theorem fixedFieldFun_apply (f : H → ℂ) (h : H) :
    fixedFieldFun H f (fixedFieldMulEquiv H h) = f h := by
  simp [fixedFieldFun]

omit [IsGalois K L] in

/- English proof (translation)
Simplify using `only [fixedFieldFun, Function.comp_apply, map_mul, map_inv]`. Conclude with `hf _ _`.
-/
theorem fixedFieldFun_conj {f : H → ℂ} (hf : IsClassFun f) (g h : Gal(L/fixedField H)) :
    fixedFieldFun H f (h * g * h⁻¹) = fixedFieldFun H f g := by
  simp only [fixedFieldFun, Function.comp_apply, map_mul, map_inv]
  exact hf _ _

/- English proof (translation)
Establish `: (x • w).asIdeal.LiesOver (subfieldPlace H w x).asIdeal` using `liesOver_subfieldPlace H w x`. Rewrite using `[localAverage_eq (subfieldPlace H w x) (fixedFieldFun H f) (fixedFieldFun_conj H hf) (x • w) (φ := fixedFieldMulEquiv H φx) ((isArithFrobAt_fixedFieldMulEquiv_iff H φx _).2 hφx) k, asIdeal_smul, inertia_fixedField_smul_eq, ← map_pow, fixedFieldFun, cosetAverage_map_mulEquiv, cose …`.
-/
theorem localAverage_subfieldPlace {f : H → ℂ} (hf : IsClassFun f) (w : HeightOneSpectrum (𝓞 L))
    (x : Gal(L/K)) (φx : H) (hφx : IsArithFrobAt (𝓞 (fixedField H)) φx (x • w.asIdeal))
    [Fintype ((MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H)]
    (k : ℕ) :
    localAverage L (subfieldPlace H w x) (fixedFieldFun H f) k =
      cosetAvg ((MulAut.conj x • w.asIdeal.inertia Gal(L/K) : Subgroup Gal(L/K)).subgroupOf H)
        φx f k := by
  have : (x • w).asIdeal.LiesOver (subfieldPlace H w x).asIdeal := liesOver_subfieldPlace H w x
  rw [localAverage_eq (subfieldPlace H w x) (fixedFieldFun H f) (fixedFieldFun_conj H hf) (x • w)
    (φ := fixedFieldMulEquiv H φx) ((isArithFrobAt_fixedFieldMulEquiv_iff H φx _).2 hφx) k,
    asIdeal_smul, inertia_fixedField_smul_eq, ← map_pow, fixedFieldFun,
    cosetAverage_map_mulEquiv, cosetAverage_pow_eq_cosetAvg]

/- English proof (translation)
Establish `h` using `card_mul_card_eq (H := H) hID x`. Use `Nat.pos_of_ne_zero fun h0 ↦ ?_` and prove the remaining obligations. Rewrite `h` using `[h0, zero_mul, zero_mul]`. Conclude with `(Nat.mul_pos Nat.card_pos Nat.card_pos).ne' h`.
-/
theorem frobIndex_pos {G : Type*} [Group G] [Finite G] {H D I : Subgroup G} (hID : I ≤ D)
    [(I.subgroupOf D).Normal] (x : G) : 0 < frobIndex H D I x := by
  have h := card_mul_card_eq (H := H) hID x
  refine Nat.pos_of_ne_zero fun h0 ↦ ?_
  rw [h0, zero_mul, zero_mul] at h
  exact (Nat.mul_pos Nat.card_pos Nat.card_pos).ne' h

/- English proof (translation)
Rewrite using `[Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]`.
-/
theorem natCast_pow_cpow_neg (N r : ℕ) (s : ℂ) :
    ((N ^ r : ℕ) : ℂ) ^ (-s) = ((N : ℂ) ^ (-s)) ^ r := by
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

open Classical in

/- English proof (translation)
Use `set w := placeAbove (L := L) v with hw`. Use `set D := MulAction.stabilizer Gal(L/K) w.asIdeal with hD`. Use `set I := w.asIdeal.inertia Gal(L/K) with hI`. Use `set φ := arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal with hφdef`. Establish `hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal` using `IsArithFrobAt.arithFrobAt _ _ _`.

Establish `hID : I ≤ D` using `Ideal.inertia_le_stabilizer w.asIdeal`. Establish `hgen` using `zpowers_arithFrob_eq_top w hφ`. Use `set r : DoubleCoset.Quotient (H : Set Gal(L/K)) D → ℕ := fun q ↦ frobIndex H D I q.out with hr`. Establish `hr0 : ∀ q, 0 < r q` using `fun q ↦ frobIndex_pos hID q.out`. Use `set φx : DoubleCoset.Quotient (H : Set Gal(L/K)) D → H := fun q ↦ (exists_frobElem_isArithFrobAt H w hφ q.out).choose with hφx`.

Establish `hφx1` using `fun q : DoubleCoset.Quotient (H : Set Gal(L/K)) D ↦ (exists_frobElem_isArithFrobAt H w hφ (Quotient.out q)).choose_spec.1`. Establish `hφx2` using `fun q : DoubleCoset.Quotient (H : Set Gal(L/K)) D ↦ (exists_frobElem_isArithFrobAt H w hφ (Quotient.out q)).choose_spec.2`. Use `set u : DoubleCoset.Quotient (H : Set Gal(L/K)) D → HeightOneSpectrum (𝓞 (fixedField H)) := fun q ↦ subfieldPlace H w q.out with hu`. Use `set f' := fixedFieldFun H f`. Use `set T : DoubleCoset.Quotient (H : Set Gal(L/K)) D → ℕ → ℂ := fun q m ↦ if r q ∣ m then artinTerm (fixedField H) L f' s (u q) (m / r q) else 0 with hT`.

Establish `hkey : ∀ (R k : ℕ) (A X : ℂ), 0 < R → (R : ℂ) * A * X ^ (R * k) / ((R * k : ℕ) : ℂ) = A * X ^ (R * k) / k`. Introduce `R k A X hR`. Break down `Nat.eq_zero_or_pos k with rfl | hk0` into its components or cases. Simplify using the standard rewrite rules. Establish `: (R : ℂ) ≠ 0` using `by exact_mod_cast hR.ne'`.

Establish `: (k : ℂ) ≠ 0` using `by exact_mod_cast hk0.ne'`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hA : ∀ m : ℕ, artinTerm K L (indFun H.subtype f) s v m = ∑ q, T q m`. Introduce `m`.

Establish `hloc : localAverage L v (indFun H.subtype f) m = cosetAvg I φ (indFun H.subtype f) (m : ℤ)` using `cosetAverage_pow_eq_cosetAvg _ _ _ _`. Rewrite using `[artinTerm, hloc, cosetAvg_indFun hID hφ.mem_stabilizer hgen hf (fun q ↦ q.out) (DoubleCoset.out_eq' _ _) φx hφx1 (m : ℤ), Finset.sum_mul, Finset.sum_div]`. Use `Finset.sum_congr rfl fun q _ ↦ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = if r q ∣ m then artinTerm (fixedField H) L f' s (u q) (m / r q) else 0`. Establish `hdvd : ((r q : ℕ) : ℤ) ∣ (m : ℤ) ↔ r q ∣ m` using `Int.natCast_dvd_natCast`.

Simplify using `only [hr] at hdvd`. Use `split_ifs with h1 h2 h2`. Take `⟨k, rfl⟩` from `h2`. Establish `hk : (((r q * k : ℕ) : ℤ) / (r q : ℤ)) = k`. Use `push_cast`.

Conclude with `Int.mul_ediv_cancel_left _ (by exact_mod_cast (hr0 q).ne')`. Simplify using `only [hr] at hk ⊢`. Rewrite using `[hk, Nat.mul_div_cancel_left _ (hr0 q), artinTerm, localAverage_subfieldPlace H hf w _ _ (hφx2 q), absNorm_subfieldPlace H v w, natCast_pow_cpow_neg, ← pow_mul]`. Conclude with `hkey _ k _ _ (hr0 q)`. Conclude with `absurd (hdvd.1 h1) h2`.

Conclude with `absurd (hdvd.2 h2) h1`. Simplify using the standard rewrite rules. Establish `hinj : ∀ q, Function.Injective fun k : ℕ ↦ r q * k` using `fun q ↦ fun a b h ↦ Nat.eq_of_mul_eq_mul_left (hr0 q) h`. Establish `hcomp : ∀ q, (T q ∘ fun k : ℕ ↦ r q * k) = fun k ↦ artinTerm (fixedField H) L f' s (u q) k` using `fun q ↦ funext fun k ↦ by`. Simplify using `only [hT, Function.comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (hr0 q)]`.

Establish `hsupp : ∀ q, Function.support (T q) ⊆ Set.range fun k : ℕ ↦ r q * k`. Introduce `q m hm`. Assume the negation of the conclusion as `hnot`. Apply `hm` to reduce the goal to its premises. Simplify using `only [hT]`.

Rewrite using `[if_neg]`. Introduce and unpack `⟨k, rfl⟩`. Conclude with `hnot ⟨k, rfl⟩`. Establish `hsum : ∀ q, Summable (T q)` using `fun q ↦ ((hinj q).summable_iff fun m hm ↦ Function.notMem_support.1 fun h ↦ hm (hsupp q h)).1 (by rw [hcomp q]; exact (hasSum_artinLocalLog f' hs (u q)).summable)`. Establish `htsum : ∀ q, ∑' m, T q m = artinLocalLog (fixedField H) L f' s (u q)` using `fun q ↦ by`.

Rewrite using `[← (hinj q).tsum_eq (hsupp q)]`. Conclude with `congrArg tsum (hcomp q)`. Rewrite using `[artinLocalLog, tsum_congr hA, Summable.tsum_finsetSum fun q _ ↦ hsum q]`. Conclude with `Finset.sum_congr rfl fun q _ ↦ htsum q`.
-/
theorem artinLocalLog_indFun [Fintype Gal(L/K)] [Fintype H] {f : H → ℂ} (hf : IsClassFun f)
    {s : ℂ} (hs : 1 < s.re) (v : HeightOneSpectrum (𝓞 K)) :
    artinLocalLog K L (indFun H.subtype f) s v =
      ∑ q : DoubleCoset.Quotient (H : Set Gal(L/K))
          (MulAction.stabilizer Gal(L/K) (placeAbove (L := L) v).asIdeal),
        artinLocalLog (fixedField H) L (fixedFieldFun H f) s
          (subfieldPlace H (placeAbove (L := L) v) q.out) := by
  set w := placeAbove (L := L) v with hw
  set D := MulAction.stabilizer Gal(L/K) w.asIdeal with hD
  set I := w.asIdeal.inertia Gal(L/K) with hI
  set φ := arithFrobAt (𝓞 K) Gal(L/K) w.asIdeal with hφdef
  have hφ : IsArithFrobAt (𝓞 K) φ w.asIdeal := IsArithFrobAt.arithFrobAt _ _ _
  have hID : I ≤ D := Ideal.inertia_le_stabilizer w.asIdeal
  have hgen := zpowers_arithFrob_eq_top w hφ
  set r : DoubleCoset.Quotient (H : Set Gal(L/K)) D → ℕ := fun q ↦ frobIndex H D I q.out with hr
  have hr0 : ∀ q, 0 < r q := fun q ↦ frobIndex_pos hID q.out
  set φx : DoubleCoset.Quotient (H : Set Gal(L/K)) D → H :=
    fun q ↦ (exists_frobElem_isArithFrobAt H w hφ q.out).choose with hφx
  have hφx1 := fun q : DoubleCoset.Quotient (H : Set Gal(L/K)) D ↦ (exists_frobElem_isArithFrobAt H w hφ (Quotient.out q)).choose_spec.1
  have hφx2 := fun q : DoubleCoset.Quotient (H : Set Gal(L/K)) D ↦ (exists_frobElem_isArithFrobAt H w hφ (Quotient.out q)).choose_spec.2
  set u : DoubleCoset.Quotient (H : Set Gal(L/K)) D → HeightOneSpectrum (𝓞 (fixedField H)) :=
    fun q ↦ subfieldPlace H w q.out with hu
  set f' := fixedFieldFun H f

  set T : DoubleCoset.Quotient (H : Set Gal(L/K)) D → ℕ → ℂ := fun q m ↦
    if r q ∣ m then artinTerm (fixedField H) L f' s (u q) (m / r q) else 0 with hT
  have hkey : ∀ (R k : ℕ) (A X : ℂ), 0 < R →
      (R : ℂ) * A * X ^ (R * k) / ((R * k : ℕ) : ℂ) = A * X ^ (R * k) / k := by
    intro R k A X hR
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    · have : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk0.ne'
      push_cast
      field_simp
  have hA : ∀ m : ℕ, artinTerm K L (indFun H.subtype f) s v m = ∑ q, T q m := by
    intro m
    have hloc : localAverage L v (indFun H.subtype f) m =
        cosetAvg I φ (indFun H.subtype f) (m : ℤ) := cosetAverage_pow_eq_cosetAvg _ _ _ _
    rw [artinTerm, hloc, cosetAvg_indFun hID hφ.mem_stabilizer hgen hf (fun q ↦ q.out)
      (DoubleCoset.out_eq' _ _) φx hφx1 (m : ℤ), Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    change _ = if r q ∣ m then artinTerm (fixedField H) L f' s (u q) (m / r q) else 0
    have hdvd : ((r q : ℕ) : ℤ) ∣ (m : ℤ) ↔ r q ∣ m := Int.natCast_dvd_natCast
    simp only [hr] at hdvd
    split_ifs with h1 h2 h2
    · obtain ⟨k, rfl⟩ := h2
      have hk : (((r q * k : ℕ) : ℤ) / (r q : ℤ)) = k := by
        push_cast
        exact Int.mul_ediv_cancel_left _ (by exact_mod_cast (hr0 q).ne')
      simp only [hr] at hk ⊢
      rw [hk, Nat.mul_div_cancel_left _ (hr0 q), artinTerm,
        localAverage_subfieldPlace H hf w _ _ (hφx2 q), absNorm_subfieldPlace H v w,
        natCast_pow_cpow_neg, ← pow_mul]
      exact hkey _ k _ _ (hr0 q)
    · exact absurd (hdvd.1 h1) h2
    · exact absurd (hdvd.2 h2) h1
    · simp

  have hinj : ∀ q, Function.Injective fun k : ℕ ↦ r q * k := fun q ↦
    fun a b h ↦ Nat.eq_of_mul_eq_mul_left (hr0 q) h
  have hcomp : ∀ q, (T q ∘ fun k : ℕ ↦ r q * k) = fun k ↦ artinTerm (fixedField H) L f' s (u q) k :=
    fun q ↦ funext fun k ↦ by
      simp only [hT, Function.comp_apply, dvd_mul_right, if_true,
        Nat.mul_div_cancel_left _ (hr0 q)]
  have hsupp : ∀ q, Function.support (T q) ⊆ Set.range fun k : ℕ ↦ r q * k := by
    intro q m hm
    by_contra hnot
    apply hm
    simp only [hT]
    rw [if_neg]
    rintro ⟨k, rfl⟩
    exact hnot ⟨k, rfl⟩
  have hsum : ∀ q, Summable (T q) := fun q ↦
    ((hinj q).summable_iff fun m hm ↦ Function.notMem_support.1 fun h ↦ hm (hsupp q h)).1
      (by rw [hcomp q]; exact (hasSum_artinLocalLog f' hs (u q)).summable)
  have htsum : ∀ q, ∑' m, T q m = artinLocalLog (fixedField H) L f' s (u q) := fun q ↦ by
    rw [← (hinj q).tsum_eq (hsupp q)]
    exact congrArg tsum (hcomp q)
  rw [artinLocalLog, tsum_congr hA, Summable.tsum_finsetSum fun q _ ↦ hsum q]
  exact Finset.sum_congr rfl fun q _ ↦ htsum q

end GroundTheory.Global.Artin
