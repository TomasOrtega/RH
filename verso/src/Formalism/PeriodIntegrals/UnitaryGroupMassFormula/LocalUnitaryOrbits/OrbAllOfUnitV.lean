import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.GenSmulMem

noncomputable section

namespace PI.OmLocU.Orb

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

def PerpG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Set (Fin n → Fv F v ⊗[F] E) :=
  {w | w ∈ latLoc (E := E) v Λ ∧ ∀ i, hR (Fv F v) σ J (X i) w = 0}

def gramG {ι : Type} (X : ι → Fin n → Fv F v ⊗[F] E) : Matrix ι ι (Fv F v ⊗[F] E) :=
  fun a b => hR (Fv F v) σ J (X a) (X b)

def UniG {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E) : Prop :=
  ∃ w ∈ OEv (E := E) v, (gramG σ J v X).det * w = 1

def UnitV : Prop :=
  StdHyp σ J ψ → (∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ) →
    IsSDLoc σ J v Λ → UnramAt (E := E) v →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E), (∀ i, X i ∈ latLoc (E := E) v Λ) →
      UniG σ J v X → Fintype.card ι < n →
      ∃ p ∈ PerpG σ J v Λ X, hR (Fv F v) σ J p p = 1 ∧ ∀ i, hR (Fv F v) σ J p (X i) = 0

/- English proof (translation)
Simplify using `only [hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem hR_smul_right (x y : Fin n → Fv F v ⊗[F] E) (c : Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x (c • y) = c * hR (Fv F v) σ J x y := by
  simp only [hR, hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Take `⟨u, -, hu⟩` from `hU`. Establish `hG : IsUnit (gramG σ J v X).det` using `⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩`. Set `eq : ι ≃ Fin n` to `Fintype.equivFinOfCardEq hc`. Set `M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)` to `Matrix.of fun i m => X (eq.symm m) i`. Establish `hA : cT (sigR (Fv F v) σ) M * JR (Fv F v) J * M = (gramG σ J v X).submatrix eq.symm eq.symm`.

Use extensionality with `p q`. Simplify using `only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Simplify using `only [M, Matrix.of_apply, gramG, hR, hform, Matrix.submatrix_apply]`. Conclude with `Finset.sum_comm`. Establish `hdA : IsUnit (cT (sigR (Fv F v) σ) M * JR (Fv F v) J).det`.

Establish `h1` using `congrArg det hA`. Rewrite `h1` using `[det_submatrix_equiv_self, det_mul]`. Rewrite `hG` using `[← h1]`. Conclude with `isUnit_of_mul_isUnit_left hG`. Establish `hB : (cT (sigR (Fv F v) σ) M * JR (Fv F v) J) *ᵥ w = 0`.

Use function extensionality and compare the values at `m`. Establish `h2` using `hw (eq.symm m)`. Simplify using `only [hR, hform] at h2`. Simplify using `only [Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply, Finset.sum_mul]`. Simplify using `only [M, Matrix.of_apply]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `h2`. Establish `h3` using `congrArg (fun y => (cT (sigR (Fv F v) σ) M * JR (Fv F v) J)⁻¹ *ᵥ y) hB`. Simplify `h3` using `[mulVec_mulVec, nonsing_inv_mul _ hdA]`.
-/
theorem perp_full {ι : Type} [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E)
    (hU : UniG σ J v X) (hc : Fintype.card ι = n) (w : Fin n → Fv F v ⊗[F] E)
    (hw : ∀ i, hR (Fv F v) σ J (X i) w = 0) : w = 0 := by
  obtain ⟨u, -, hu⟩ := hU
  have hG : IsUnit (gramG σ J v X).det := ⟨⟨_, u, hu, by rw [mul_comm]; exact hu⟩, rfl⟩
  let eq : ι ≃ Fin n := Fintype.equivFinOfCardEq hc
  let M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i m => X (eq.symm m) i
  have hA : cT (sigR (Fv F v) σ) M * JR (Fv F v) J * M = (gramG σ J v X).submatrix eq.symm eq.symm := by
    ext p q
    simp only [cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply, gramG, hR, hform, Matrix.submatrix_apply]
    exact Finset.sum_comm
  have hdA : IsUnit (cT (sigR (Fv F v) σ) M * JR (Fv F v) J).det := by
    have h1 := congrArg det hA
    rw [det_submatrix_equiv_self, det_mul] at h1
    rw [← h1] at hG
    exact isUnit_of_mul_isUnit_left hG
  have hB : (cT (sigR (Fv F v) σ) M * JR (Fv F v) J) *ᵥ w = 0 := by
    funext m
    have h2 := hw (eq.symm m)
    simp only [hR, hform] at h2
    simp only [Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Pi.zero_apply, Finset.sum_mul]
    simp only [M, Matrix.of_apply]
    rw [Finset.sum_comm]
    exact h2
  have h3 := congrArg (fun y => (cT (sigR (Fv F v) σ) M * JR (Fv F v) J)⁻¹ *ᵥ y) hB
  simpa [mulVec_mulVec, nonsing_inv_mul _ hdA] using h3

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `ι _ _ X hc hX hUX`. Use `⟨Fin.elim0, fun j => j.elim0, fun i j => j.elim0, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `i`. Conclude with `i.elim0`. Introduce `w hw`. Use `⟨Fin.elim0, fun j => j.elim0, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.univ_eq_empty, Finset.sum_empty]`.

Conclude with `perp_full σ J v X hUX (by omega) w hw.2`. Consider the case `succ k ih`. Introduce `ι _ _ X hc hX hUX`. Take `⟨p, hp, hpp, hpX⟩` from `hU hstd hL hsd hun ι X hX hUX (by omega)`. Set `X' : ι ⊕ Unit → Fin n → Fv F v ⊗[F] E` to `Sum.elim X (fun _ => p)`.

Establish `hG' : gramG σ J v X' = Matrix.fromBlocks (gramG σ J v X) 0 0 1`. Use extensionality with `s t`. Apply the tactic sequence `rcases s with i | ⟨⟩ <;> rcases t with j | ⟨⟩`. Both sides reduce to the same expression. Simplify using `[gramG, X', hp.2 i]`.

Simplify using `[gramG, X', hpX j]`. Simplify using `[gramG, X', hpp]`. Establish `hU' : UniG σ J v X'`. Take `⟨u, hu0, hu⟩` from `hUX`. Use `⟨u, hu0, ?_⟩` and prove the remaining obligations.

Rewrite using `[hG', det_fromBlocks_zero₂₁, det_one, mul_one, hu]`. Establish `hX' : ∀ s, X' s ∈ latLoc (E` using `E) v Λ := by`. Introduce and unpack `(i | ⟨⟩)`. Conclude with `hX i`. Conclude with `hp.1`.

Take `⟨e', he'P, he'X, he'e, he'span⟩` from `ih (ι ⊕ Unit) X' (by rw [Fintype.card_sum, Fintype.card_unit]; omega) hX' hU'`. Use `⟨Fin.cons p e', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`. Use `Fin.cases hp (fun j => ⟨(he'P j).1, fun i => (he'P j).2 (Sum.inl i)⟩) j` and prove the remaining obligations. Introduce `i j`.

Use `Fin.cases (hpX i) (fun j => he'X (Sum.inl i) j) j` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j`. Simplify `hpp` using `[gramR]`. Establish `h1 : hR (Fv F v) σ J p (e' j) = 0` using `(he'P j).2 (Sum.inr ())`.

Simplify `h1` using `[gramR, Matrix.one_apply, (Fin.succ_ne_zero j).symm]`. Establish `h1 : hR (Fv F v) σ J (e' i) p = 0` using `he'X (Sum.inr ()) i`. Simplify `h1` using `[gramR, Matrix.one_apply, Fin.succ_ne_zero]`. Simplify `congrFun (congrFun he'e i) j` using `[gramR, Matrix.one_apply]`. Introduce `w hw set c := hR (Fv F v) σ J p w with hcdef`.

Establish `hc0 : c ∈ OEv (E` using `E) v := (hsd w).1 hw.1 p hp.1`. Establish `hw' : w - c • p ∈ PerpG σ J v Λ X'`. Use `⟨Submodule.sub_mem _ hw.1 (oSmul v Λ hL c hc0 p hp.1), ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | ⟨⟩)`. Use `show hR (Fv F v) σ J (X i) (w - c • p) = 0`.

Rewrite using `[hR_sub_right, hR_smul_right, hw.2 i, hp.2 i, mul_zero, sub_zero]`. Use `show hR (Fv F v) σ J p (w - c • p) = 0`. Rewrite using `[hR_sub_right, hR_smul_right, hpp, mul_one, ← hcdef, sub_self]`. Take `⟨d', hd'O, hd'⟩` from `he'span _ hw'`. Use `⟨Fin.cons c d', fun j => Fin.cases hc0 hd'O j, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[← hd']`. Normalize the expressions using the abelian group laws.
-/
theorem orthoGen (hU : UnitV σ J ψ v Λ) (hstd : StdHyp σ J ψ)
    (hL : ∃ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L ∧ (L : Set (Fin n → E)) = Λ)
    (hsd : IsSDLoc σ J v Λ) (hun : UnramAt (E := E) v) :
    ∀ (k : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (X : ι → Fin n → Fv F v ⊗[F] E),
      Fintype.card ι + k = n → (∀ i, X i ∈ latLoc (E := E) v Λ) → UniG σ J v X →
      ∃ e : Fin k → Fin n → Fv F v ⊗[F] E, (∀ j, e j ∈ PerpG σ J v Λ X) ∧
        (∀ i j, hR (Fv F v) σ J (e j) (X i) = 0) ∧ gramR (Fv F v) σ J e = 1 ∧
        ∀ w ∈ PerpG σ J v Λ X, ∃ d : Fin k → Fv F v ⊗[F] E, (∀ j, d j ∈ OEv (E := E) v) ∧
          w = ∑ j, d j • e j := by
  intro k
  induction k with
  | zero =>
    intro ι _ _ X hc hX hUX
    refine ⟨Fin.elim0, fun j => j.elim0, fun i j => j.elim0, ?_, ?_⟩
    · ext i
      exact i.elim0
    · intro w hw
      refine ⟨Fin.elim0, fun j => j.elim0, ?_⟩
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact perp_full σ J v X hUX (by omega) w hw.2
  | succ k ih =>
    intro ι _ _ X hc hX hUX
    obtain ⟨p, hp, hpp, hpX⟩ := hU hstd hL hsd hun ι X hX hUX (by omega)
    let X' : ι ⊕ Unit → Fin n → Fv F v ⊗[F] E := Sum.elim X (fun _ => p)
    have hG' : gramG σ J v X' = Matrix.fromBlocks (gramG σ J v X) 0 0 1 := by
      ext s t
      rcases s with i | ⟨⟩ <;> rcases t with j | ⟨⟩
      · rfl
      · simp [gramG, X', hp.2 i]
      · simp [gramG, X', hpX j]
      · simp [gramG, X', hpp]
    have hU' : UniG σ J v X' := by
      obtain ⟨u, hu0, hu⟩ := hUX
      refine ⟨u, hu0, ?_⟩
      rw [hG', det_fromBlocks_zero₂₁, det_one, mul_one, hu]
    have hX' : ∀ s, X' s ∈ latLoc (E := E) v Λ := by
      rintro (i | ⟨⟩)
      · exact hX i
      · exact hp.1
    obtain ⟨e', he'P, he'X, he'e, he'span⟩ :=
      ih (ι ⊕ Unit) X' (by rw [Fintype.card_sum, Fintype.card_unit]; omega) hX' hU'
    refine ⟨Fin.cons p e', ?_, ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases hp (fun j => ⟨(he'P j).1, fun i => (he'P j).2 (Sum.inl i)⟩) j
    · intro i j
      refine Fin.cases (hpX i) (fun j => he'X (Sum.inl i) j) j
    · ext i j
      refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
      · simpa [gramR] using hpp
      · have h1 : hR (Fv F v) σ J p (e' j) = 0 := (he'P j).2 (Sum.inr ())
        simpa [gramR, Matrix.one_apply, (Fin.succ_ne_zero j).symm] using h1
      · have h1 : hR (Fv F v) σ J (e' i) p = 0 := he'X (Sum.inr ()) i
        simpa [gramR, Matrix.one_apply, Fin.succ_ne_zero] using h1
      · simpa [gramR, Matrix.one_apply] using congrFun (congrFun he'e i) j
    · intro w hw
      set c := hR (Fv F v) σ J p w with hcdef
      have hc0 : c ∈ OEv (E := E) v := (hsd w).1 hw.1 p hp.1
      have hw' : w - c • p ∈ PerpG σ J v Λ X' := by
        refine ⟨Submodule.sub_mem _ hw.1 (oSmul v Λ hL c hc0 p hp.1), ?_⟩
        rintro (i | ⟨⟩)
        · show hR (Fv F v) σ J (X i) (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hw.2 i, hp.2 i, mul_zero, sub_zero]
        · show hR (Fv F v) σ J p (w - c • p) = 0
          rw [hR_sub_right, hR_smul_right, hpp, mul_one, ← hcdef, sub_self]
      obtain ⟨d', hd'O, hd'⟩ := he'span _ hw'
      refine ⟨Fin.cons c d', fun j => Fin.cases hc0 hd'O j, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hd']
      abel

/- English proof (translation)
Introduce `h hG X hX hXY`. Take `⟨w, hw0, -, hw⟩` from `hG.2.2.2.2.2.2`. Rewrite `hw` using `[← hXY]`. Conclude with `orthoGen σ J ψ v Λ hU hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 (n - a) (Fin a) X (by rw [Fintype.card_fin]; omega) hX ⟨w, hw0, hw⟩`.
-/
theorem orthoB_of (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrthoB σ J ψ v Λ a Y := by
  intro h hG X hX hXY
  obtain ⟨w, hw0, -, hw⟩ := hG.2.2.2.2.2.2
  rw [← hXY] at hw
  exact orthoGen σ J ψ v Λ hU hG.1 hG.2.1 hG.2.2.1 hG.2.2.2.1 (n - a) (Fin a) X
    (by rw [Fintype.card_fin]; omega) hX ⟨w, hw0, hw⟩

/- English proof (translation)
The claim follows from `orbAll_of_orthoB σ J ψ v Λ a Y (oSub v) (oSmul v Λ) (orthoB_of σ J ψ v Λ a Y hU)`.
-/
theorem orbAll_of_unitV (a : ℕ) (Y : TupV (E := E) v n a) (hU : UnitV σ J ψ v Λ) : OrbAll σ J ψ v Λ a Y :=
  orbAll_of_orthoB σ J ψ v Λ a Y (oSub v) (oSmul v Λ) (orthoB_of σ J ψ v Λ a Y hU)

end PI.OmLocU.Orb
