import Development.WeilBound.ThetaLifts.SphericalLattices.FunDefs
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix TensorProduct
open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.InertChart GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
  PositivityTheory.ThK PositivityTheory.ThKH.Iwas GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

section Abstract

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {c : L →+* L}

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, antiJ]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem antiJ_map_cart2 (n : ℕ) : (antiJ L n).map c = antiJ L n := by
  ext i j
  simp only [Matrix.map_apply, antiJ]
  split_ifs <;> simp

omit [Valued L (WithZero (Multiplicative ℤ))] in
/- English proof (translation)
Establish `hcc : ∀ N : Matrix (Fin n) (Fin n) L, (N.map c).map c = N` using `fun N => Matrix.ext fun i j => hc _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg (fun N => N.map c) h` as an intermediate fact. Simplify using `only [Matrix.map_mul, antiJ_map_cart2, hcc] at this`.

Conclude with `this`. Introduce `h`. Use `congrArg (fun N => N.map c) h` as an intermediate fact. Simplify using `only [Matrix.map_mul, antiJ_map_cart2] at this`. Rewrite `this` using `[cT, Matrix.transpose_map, hcc]`.

Conclude with `this`.
-/
theorem iso_cT_cart2 (hc : ∀ x, c (c x) = x) {n : ℕ} (M : Matrix (Fin n) (Fin n) L) :
    Iso c (antiJ L n) (antiJ L n) M ↔ cT c M * antiJ L n * M = antiJ L n := by
  have hcc : ∀ N : Matrix (Fin n) (Fin n) L, (N.map c).map c = N := fun N => Matrix.ext fun i j => hc _
  constructor
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2, hcc] at this
    exact this
  · intro h
    have := congrArg (fun N => N.map c) h
    simp only [Matrix.map_mul, antiJ_map_cart2] at this
    rw [cT, Matrix.transpose_map, hcc] at this
    exact this

/- English proof (translation)
Establish `hcc : ∀ x, c (c x) = x` using `hU.1`. Establish `hint : ∀ i j, antiJ L n i j ∈ intL L`. Introduce `i j`. Unfold `antiJ`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Take `⟨J, hJ, hJe⟩` from `P.cartan_exists_glint (intL L) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint`. Establish `hherm : ∀ i j, c ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i`. Introduce `i j`.

Rewrite using `[hJe]`. Simplify using `only [antiJ, add_comm i.val j.val]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `h hh`. Set `g : GL (Fin n) L` to `Φ.toHomUnits h`.

Establish `eg : ∀ x : G, ((Φ.toHomUnits x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Φ x` using `fun _ => rfl`. Establish `hg : g ∈ UJ c (J : Matrix (Fin n) (Fin n) L)` using `by show cT c (g : Matrix (Fin n) (Fin n) L) * _ * (g : Matrix (Fin n) (Fin n) L) = _`. Rewrite using `[hJe, eg]`. Conclude with `(iso_cT_cart2 hcc _).1 (hiso h)`. Take `⟨k₁, hk₁, k₂, hk₂, e⟩` from `GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ hherm hg`.

Establish `hkU : ∀ k ∈ UJ c (J : Matrix (Fin n) (Fin n) L), Iso c (antiJ L n) (antiJ L n) (k : Matrix (Fin n) (Fin n) L)` using `fun k hk => (iso_cT_cart2 hcc _).2 (by rw [← hJe]; exact hk)`. Take `⟨g₁, hg₁, e₁⟩` from `surj _ (hkU k₁ hk₁.1)`. Take `⟨g₂, hg₂, e₂⟩` from `surj _ (hkU k₂ hk₂.1)`. Establish `memK : ∀ (x : G) (k : GL (Fin n) L), x ∈ U → Φ x = k → k ∈ GLint (Fin n) (intL L) → x ∈ K`. Introduce `x k hx ex hk`.

Establish `einv : Φ x⁻¹ = ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ex, Units.mul_inv, Matrix.mul_one]`. Use `_ = _ := by rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]`. Use `(hK x).2 ⟨hx, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations.

Rewrite using `[ex]`. Conclude with `P.cartan_entries_of_mem _ _ hk i j`. Rewrite using `[einv]`. Conclude with `P.cartan_entries_of_mem _ _ (inv_mem hk) i j`. Use `⟨g₁, memK _ _ hg₁ e₁ hk₁.2, g₂, memK _ _ hg₂ e₂ hk₂.2, inj _ (inv_mem hh) _ (mul_mem (mul_mem hg₁ hh) hg₂) ?_⟩` and prove the remaining obligations.

Establish `e'` using `congrArg (fun x : GL (Fin n) L => (x : Matrix (Fin n) (Fin n) L)) e`. Simplify using `only [Units.val_mul] at e'`. Rewrite using `[map_mul, map_mul, e₁, e₂, ← eg h⁻¹, map_inv]`. Conclude with `e'`.
-/
theorem inv_mem_KgK_cart2 {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ c q) {n : ℕ} {G : Type} [Group G] (U : Subgroup G)
    (Φ : G →* Matrix (Fin n) (Fin n) L) (hiso : ∀ g, Iso c (antiJ L n) (antiJ L n) (Φ g))
    (inj : ∀ g ∈ U, ∀ g' ∈ U, Φ g = Φ g' → g = g')
    (surj : ∀ M, Iso c (antiJ L n) (antiJ L n) M → ∃ g ∈ U, Φ g = M) (K : Set G)
    (hK : ∀ g, g ∈ K ↔ g ∈ U ∧ (∀ i j, Valued.v (Φ g i j) ≤ 1) ∧ ∀ i j, Valued.v (Φ g⁻¹ i j) ≤ 1) :
    ∀ h ∈ U, ∃ k₁ ∈ K, ∃ k₂ ∈ K, h⁻¹ = k₁ * h * k₂ := by
  have hcc : ∀ x, c (c x) = x := hU.1
  have hint : ∀ i j, antiJ L n i j ∈ intL L := by
    intro i j; unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨J, hJ, hJe⟩ := P.cartan_exists_glint (intL L) _ _ (GlobalTheory.UnitarySwap.antiJ_mul_self (L := L) (n := n)) hint hint
  have hherm : ∀ i j, c ((J : Matrix (Fin n) (Fin n) L) i j) = (J : Matrix (Fin n) (Fin n) L) j i := by
    intro i j
    rw [hJe]
    simp only [antiJ, add_comm i.val j.val]
    split_ifs <;> simp
  intro h hh
  let g : GL (Fin n) L := Φ.toHomUnits h
  have eg : ∀ x : G, ((Φ.toHomUnits x : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Φ x := fun _ => rfl
  have hg : g ∈ UJ c (J : Matrix (Fin n) (Fin n) L) := by
    show cT c (g : Matrix (Fin n) (Fin n) L) * _ * (g : Matrix (Fin n) (Fin n) L) = _
    rw [hJe, eg]
    exact (iso_cT_cart2 hcc _).1 (hiso h)
  obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.UnitarySwap.inv_mem_doubleCoset hU hJ hherm hg
  have hkU : ∀ k ∈ UJ c (J : Matrix (Fin n) (Fin n) L), Iso c (antiJ L n) (antiJ L n) (k : Matrix (Fin n) (Fin n) L) :=
    fun k hk => (iso_cT_cart2 hcc _).2 (by rw [← hJe]; exact hk)
  obtain ⟨g₁, hg₁, e₁⟩ := surj _ (hkU k₁ hk₁.1)
  obtain ⟨g₂, hg₂, e₂⟩ := surj _ (hkU k₂ hk₂.1)
  have memK : ∀ (x : G) (k : GL (Fin n) L), x ∈ U → Φ x = k → k ∈ GLint (Fin n) (intL L) → x ∈ K := by
    intro x k hx ex hk
    have einv : Φ x⁻¹ = ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
      calc Φ x⁻¹ = Φ x⁻¹ * (Φ x * ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [ex, Units.mul_inv, Matrix.mul_one]
        _ = _ := by rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    refine (hK x).2 ⟨hx, fun i j => ?_, fun i j => ?_⟩
    · rw [ex]; exact P.cartan_entries_of_mem _ _ hk i j
    · rw [einv]; exact P.cartan_entries_of_mem _ _ (inv_mem hk) i j
  refine ⟨g₁, memK _ _ hg₁ e₁ hk₁.2, g₂, memK _ _ hg₂ e₂ hk₂.2,
    inj _ (inv_mem hh) _ (mul_mem (mul_mem hg₁ hh) hg₂) ?_⟩
  have e' := congrArg (fun x : GL (Fin n) L => (x : Matrix (Fin n) (Fin n) L)) e
  simp only [Units.val_mul] at e'
  rw [map_mul, map_mul, e₁, e₂, ← eg h⁻¹, map_inv]
  exact e'

end Abstract

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d B W r s hB hW _ v w hw hh`. Establish `hσ` using `hB.cm`. Establish `hu : w.under (𝓞 F) = v` using `(under_eq_iff hw w).2 rfl`. Take `⟨c, hc, -⟩` from `existsUnique_isConjAt σ hw hu`. Take `⟨ϖ, hU⟩` from `exists_isUnramInv hσ hw hc`.

Take `⟨a, ha, l, hl, hg⟩` from `exists_frame hσ hw hu hc hW`. Establish `hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ d) a.1` using `hg`. Establish `one : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (piE hu) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Set `Φ : UA σ W.J →* Matrix (Fin d) (Fin d) (w.adicCompletion E)` to `{ toFun := fun g => (a⁻¹).1 * (mat g).map (piE hu) * a.1 map_one' := by`. Rewrite using `[show mat (1 : UA σ W.J) = 1 from rfl, one, Matrix.mul_one, Units.inv_mul]`.

Use the proof step `map_mul' := fun g g' => by`. Rewrite using `[show mat (g * g') = mat g * mat g' from rfl, Matrix.map_mul]`. Simplify using `only [Matrix.mul_assoc, Units.mul_inv_cancel_left] }`. Establish `hΦ : ∀ g, Φ g = (a⁻¹).1 * (mat g).map (piE hu) * a.1` using `fun _ => rfl`. Establish `hint : ∀ g, (∀ i j, Valued.v (Φ g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v` using `fun g => by`.

Rewrite using `[stab_iff hw hu ha]`. Conclude with `Iff.rfl`. Use `inv_mem_KgK_cart2 hU (USub σ W v) Φ (fun g => ?_) (fun g hg g' hg' e => ?_) (fun N hN => ?_) _ (fun g => ?_) hh` and prove the remaining obligations. Establish `h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE hu))`. Unfold `Iso`.

Rewrite using `[← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]`. Conclude with `Matrix.ext fun i j => piE_incl hu _`. Rewrite using `[hΦ]`. Conclude with `(iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai)`. Establish `e1 : (mat g).map (piE hu) = (mat g').map (piE hu)`.

Establish `e2` using `congrArg (fun N => a.1 * N * (a⁻¹).1) e`. Simplify `e2` using `[hΦ, Matrix.mul_assoc]`. Use `Subtype.ext (Units.ext (mat_inj hw hu ?_ e1))` and prove the remaining obligations. Use `at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Establish `h2` using `(hai.mul ((iso_smul_iff hl _ _).2 hN)).mul (hai.inv a.mul_inv)`. Establish `h3` using `h2.isUnit_det (by`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `((map_ne_zero _).2 (PositivityTheory.ThKH.Iwas.det_ne_zero hW)).isUnit)`. Take `⟨k, hk, ek⟩` from `exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2`.

Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, ek]`. Simplify using `[Matrix.mul_assoc]`. Rewrite using `[hint, hint]`. Conclude with `and_congr Iff.rfl ⟨fun H => ⟨fun y hy => (H y hy).1, fun y hy => (H y hy).2⟩, fun H y hy => ⟨H.1 y hy, H.2 y hy⟩⟩`.
-/
theorem cartanSt2 : CartanSt := by
  intro F E _ _ _ _ _ σ d B W r s hB hW _ v w hw hh
  have hσ := hB.cm
  have hu : w.under (𝓞 F) = v := (under_eq_iff hw w).2 rfl
  obtain ⟨c, hc, -⟩ := existsUnique_isConjAt σ hw hu
  obtain ⟨ϖ, hU⟩ := exists_isUnramInv hσ hw hc
  obtain ⟨a, ha, l, hl, hg⟩ := exists_frame hσ hw hu hc hW
  have hai : Iso c (W.J.map (algebraMap E _)) (l • antiJ _ d) a.1 := hg
  have one : (1 : Matrix (Fin d) (Fin d) (AE F E)).map (piE hu) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  let Φ : UA σ W.J →* Matrix (Fin d) (Fin d) (w.adicCompletion E) :=
    { toFun := fun g => (a⁻¹).1 * (mat g).map (piE hu) * a.1
      map_one' := by
        rw [show mat (1 : UA σ W.J) = 1 from rfl, one, Matrix.mul_one, Units.inv_mul]
      map_mul' := fun g g' => by
        rw [show mat (g * g') = mat g * mat g' from rfl, Matrix.map_mul]
        simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left] }
  have hΦ : ∀ g, Φ g = (a⁻¹).1 * (mat g).map (piE hu) * a.1 := fun _ => rfl
  have hint : ∀ g, (∀ i j, Valued.v (Φ g i j) ≤ 1) ↔ ∀ y ∈ latW W v, mat g *ᵥ y ∈ latW W v := fun g => by
    rw [stab_iff hw hu ha]
    exact Iff.rfl
  refine inv_mem_KgK_cart2 hU (USub σ W v) Φ (fun g => ?_) (fun g hg g' hg' e => ?_) (fun N hN => ?_) _ (fun g => ?_) hh
  · have h1 : Iso c (W.J.map (algebraMap E _)) (W.J.map (algebraMap E _)) ((mat g).map (piE hu)) := by
      unfold Iso
      rw [← map_gram hc, show (mat g)ᵀ * incM F W.J * (mat g).map (cA σ) = incM F W.J from g.2]
      exact Matrix.ext fun i j => piE_incl hu _
    rw [hΦ]
    exact (iso_smul_iff hl _ _).1 (((hai.inv a.mul_inv).mul h1).mul hai)
  · have e1 : (mat g).map (piE hu) = (mat g').map (piE hu) := by
      have e2 := congrArg (fun N => a.1 * N * (a⁻¹).1) e
      simpa [hΦ, Matrix.mul_assoc] using e2
    refine Subtype.ext (Units.ext (mat_inj hw hu ?_ e1))
    have := at_sub (show At (evFin F v) (mat g - 1) from hg) (show At (evFin F v) (mat g' - 1) from hg')
    rwa [sub_sub_sub_cancel_right] at this
  · have h2 := (hai.mul ((iso_smul_iff hl _ _).2 hN)).mul (hai.inv a.mul_inv)
    have h3 := h2.isUnit_det (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact ((map_ne_zero _).2 (PositivityTheory.ThKH.Iwas.det_ne_zero hW)).isUnit)
    obtain ⟨k, hk, ek⟩ := exists_lift_UA hw hc W (Matrix.mul_nonsing_inv _ h3) h2
    refine ⟨k, hk, ?_⟩
    rw [hΦ, ek]
    simp [Matrix.mul_assoc]
  · rw [hint, hint]
    exact and_congr Iff.rfl ⟨fun H => ⟨fun y hy => (H y hy).1, fun y hy => (H y hy).2⟩, fun H y hy => ⟨H.1 y hy, H.2 y hy⟩⟩

end PositivityTheory.Sph

end
