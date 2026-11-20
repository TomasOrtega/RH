import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.ChainInst
import Formalism.LocalToGlobal.Columns.TiedValRat
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusNoKernelOfFrobeniusSimilitude

noncomputable section

namespace GlobalTheory.Mem.Col2.RowTie

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

local notation "ιA" => inclE (F := F) (FiniteAdeleRing (𝓞 F) F)

omit [NumberField E] in
/- English proof (translation)
Simplify using `only [atInf, Units.val_mul, Matrix.map_mul]`.
-/
theorem atInf_mul (emb : ι → E →+* ℂ) (γ δ : GL (Fin n) E) (τ : ι) :
    atInf emb ((γ * δ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ =
      atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb (δ : Matrix (Fin n) (Fin n) E) τ := by
  simp only [atInf, Units.val_mul, Matrix.map_mul]

omit [NumberField E] in
/- English proof (translation)
Simplify using `[atInf]`.
-/
theorem atInf_one (emb : ι → E →+* ℂ) (τ : ι) :
    atInf emb ((1 : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp [atInf]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, ⟨h1, h2⟩, rfl⟩ c`. Conclude with `⟨h2 (y c) trivial, fun γ hγ κ e z z' hz => h1 γ hγ (y c) (y c) κ e z z' hz⟩`. Introduce `H`. Establish `hdec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ c, ∃ γ : GL (Fin n) E, ∃ _ : γ ∈ UJ (σ : E →+* E) J, ∃ κ : S.U, x.1 = bc ιA γ * (y c).1 * κ.1`.

Introduce `x`. Take `⟨c, hcx⟩` from `hy.2 (Quotient.mk'' x)`. Take `⟨hh, hhH, κ, hκK, e⟩` from `(DoubleCoset.eq _ _ (y c) x).1 hcx`. Take `⟨g, hgU, hge⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)`. Use `⟨c, g, hgU, ⟨κ.1, hκK⟩, ?_⟩` and prove the remaining obligations.

Use `congrArg Subtype.val e` as an intermediate fact. Simplify using `only [Subgroup.coe_mul] at this`. Rewrite using `[this, hge]`. Use `choose cx γx hγx κx hx using hdec`. Establish `hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)` using `fun κ => ((S.U_eq κ.1).1 κ.2).1`.

Set `g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ` to `fun x z => (S.chi (κx x) : ℂ) * φ (cx x) (z.tr _ (isUnit_det_atInf emb (γx x)⁻¹))`. Establish `key : ∀ x c γ, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U, x.1 = bc ιA γ * (y c).1 * κ.1 → ∀ z z' : Frames (gramC J emb), IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z' z → g x z = (S.chi κ : ℂ) * φ c z'`. Introduce `x c γ hγ κ e z z' hz`. Establish `e1 : (y c).1 = bc ιA (γ⁻¹ * γx x) * (y (cx x)).1 * (κx x * κ⁻¹ : S.U).1`. Establish `e2 : (y c).1 = (bc ιA γ)⁻¹ * x.1 * κ.1⁻¹` using `by rw [e]; group`.

Rewrite using `[e2, hx x, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]`. Use `group`. Establish `hm` using `mul_mem (inv_mem hγ) (hγx x)`. Establish `hc : cx x = c`. Apply `hy.1` to reduce the goal to its premises.

Set `k : UPts σ J (FiniteAdeleRing (𝓞 F) F)` to `⟨_, hU (κx x * κ⁻¹)⟩`. Use `(DoubleCoset.eq _ _ (y (cx x)) (y c)).2 ⟨y c * k⁻¹ * (y (cx x))⁻¹, ?_, k, ?_, by group⟩` and prove the remaining obligations. Use `Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨_, hm, ?_⟩) show _ = (y c).1 * ((κx x * κ⁻¹ : S.U).1)⁻¹ * ((y (cx x)).1)⁻¹` and prove the remaining obligations. Rewrite using `[e1]`. Use `group`.

Conclude with `Subgroup.mem_subgroupOf.2 (κx x * κ⁻¹).2`. Substitute `hc` using the available equality. Establish `h3` using `(H _).2 _ hm _ e1 z' (z.tr _ (isUnit_det_atInf emb (γx x)⁻¹)) fun τ => by show _ = _ * (_ * z.1 τ)`. Rewrite using `[hz τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← atInf_mul, ← atInf_mul, mul_inv_cancel_right, inv_mul_cancel, atInf_one, Matrix.one_mul]`. Rewrite using `[h3, ← mul_assoc, ← Units.val_mul, map_mul, map_inv, mul_comm (S.chi (κx x)), mul_inv_cancel_left]`.

Use `⟨g, ⟨?_, fun x _ => ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `γ hγ x x' κ e z z' hz`. Rewrite using `[key x' (cx x) (γ * γx x) (mul_mem hγ (hγx x)) (κx x * κ) (by`. Rewrite using `[e, hx x, map_mul, Subgroup.coe_mul]; group) z (z'.tr _ (isUnit_det_atInf emb (γx x)⁻¹)) fun τ => by show _ = _ * (_ * z'.1 τ)`. Rewrite using `[hz τ, ← Matrix.mul_assoc, ← atInf_mul, mul_inv_cancel_right], map_mul, Units.val_mul]`.

Simplify using `only [g]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨P, hP, e⟩` from `Submodule.mem_map.1 (H (cx x)).1`. Use `Submodule.smul_mem _ (S.chi (κx x) : ℂ) (Submodule.mem_map.2 ⟨_, Submodule.smul_mem _ (∏ τ, (atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ).det ^ shiftOf lam τ) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.complex_span_block_action_stable lam (atInf emb …` and prove the remaining obligations. Rewrite using `[← fnOf_mul, ← e]`.

Use function extensionality and compare the values at `z`. Simplify using `only [fnOf, Frames.tr, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.mul_one, Matrix.one_mul]`. Use function extensionality and compare the values at `c z`. Use `key (y c) c 1 (one_mem _) 1 (by simp) z z fun τ => by rw [atInf_one, Matrix.one_mul]` as an intermediate fact. Rewrite `this` using `[map_one, Units.val_one, one_mul]`.

Conclude with `this`.
-/
theorem mem_FiC_iff (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ) (lam : ι → DomWeight n) {C : Type}
    (y : C → UPts σ J (FiniteAdeleRing (𝓞 F) F)) (hy : Function.Bijective fun c => (Quotient.mk'' (y c) : Cls S))
    (φ : C → Frames (gramC J emb) → ℂ) :
    φ ∈ FiC S emb lam y ↔ ∀ c, φ c ∈ ValC (gramC J emb) lam ∧ ∀ γ ∈ UJ (σ : E →+* E) J, ∀ κ : S.U,
      (y c).1 = bc ιA γ * (y c).1 * κ.1 → ∀ z z' : Frames (gramC J emb),
        IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z' z → φ c z = (S.chi κ : ℂ) * φ c z' := by
  constructor
  · rintro ⟨g, ⟨h1, h2⟩, rfl⟩ c
    exact ⟨h2 (y c) trivial, fun γ hγ κ e z z' hz => h1 γ hγ (y c) (y c) κ e z z' hz⟩
  intro H
  have hdec : ∀ x : UPts σ J (FiniteAdeleRing (𝓞 F) F), ∃ c, ∃ γ : GL (Fin n) E, ∃ _ : γ ∈ UJ (σ : E →+* E) J,
      ∃ κ : S.U, x.1 = bc ιA γ * (y c).1 * κ.1 := by
    intro x
    obtain ⟨c, hcx⟩ := hy.2 (Quotient.mk'' x)
    obtain ⟨hh, hhH, κ, hκK, e⟩ := (DoubleCoset.eq _ _ (y c) x).1 hcx
    obtain ⟨g, hgU, hge⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhH)
    refine ⟨c, g, hgU, ⟨κ.1, hκK⟩, ?_⟩
    have := congrArg Subtype.val e
    simp only [Subgroup.coe_mul] at this
    rw [this, hge]
  choose cx γx hγx κx hx using hdec
  have hU : ∀ κ : S.U, κ.1 ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) := fun κ => ((S.U_eq κ.1).1 κ.2).1
  let g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ := fun x z =>
    (S.chi (κx x) : ℂ) * φ (cx x) (z.tr _ (isUnit_det_atInf emb (γx x)⁻¹))
  have key : ∀ x c γ, γ ∈ UJ (σ : E →+* E) J → ∀ κ : S.U, x.1 = bc ιA γ * (y c).1 * κ.1 → ∀ z z' : Frames (gramC J emb),
      IsTr (atInf emb (γ : Matrix (Fin n) (Fin n) E)) z' z → g x z = (S.chi κ : ℂ) * φ c z' := by
    intro x c γ hγ κ e z z' hz
    have e1 : (y c).1 = bc ιA (γ⁻¹ * γx x) * (y (cx x)).1 * (κx x * κ⁻¹ : S.U).1 := by
      have e2 : (y c).1 = (bc ιA γ)⁻¹ * x.1 * κ.1⁻¹ := by rw [e]; group
      rw [e2, hx x, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hm := mul_mem (inv_mem hγ) (hγx x)
    have hc : cx x = c := by
      apply hy.1
      let k : UPts σ J (FiniteAdeleRing (𝓞 F) F) := ⟨_, hU (κx x * κ⁻¹)⟩
      refine (DoubleCoset.eq _ _ (y (cx x)) (y c)).2 ⟨y c * k⁻¹ * (y (cx x))⁻¹, ?_, k, ?_, by group⟩
      · refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨_, hm, ?_⟩)
        show _ = (y c).1 * ((κx x * κ⁻¹ : S.U).1)⁻¹ * ((y (cx x)).1)⁻¹
        rw [e1]
        group
      · exact Subgroup.mem_subgroupOf.2 (κx x * κ⁻¹).2
    subst hc
    have h3 := (H _).2 _ hm _ e1 z' (z.tr _ (isUnit_det_atInf emb (γx x)⁻¹)) fun τ => by
      show _ = _ * (_ * z.1 τ)
      rw [hz τ, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← atInf_mul, ← atInf_mul, mul_inv_cancel_right, inv_mul_cancel,
        atInf_one, Matrix.one_mul]
    rw [h3, ← mul_assoc, ← Units.val_mul, map_mul, map_inv, mul_comm (S.chi (κx x)), mul_inv_cancel_left]
  refine ⟨g, ⟨?_, fun x _ => ?_⟩, ?_⟩
  · intro γ hγ x x' κ e z z' hz
    rw [key x' (cx x) (γ * γx x) (mul_mem hγ (hγx x)) (κx x * κ) (by
      rw [e, hx x, map_mul, Subgroup.coe_mul]; group) z (z'.tr _ (isUnit_det_atInf emb (γx x)⁻¹)) fun τ => by
        show _ = _ * (_ * z'.1 τ)
        rw [hz τ, ← Matrix.mul_assoc, ← atInf_mul, mul_inv_cancel_right], map_mul, Units.val_mul]
    simp only [g]
    ring
  · obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 (H (cx x)).1
    refine Submodule.smul_mem _ (S.chi (κx x) : ℂ) (Submodule.mem_map.2 ⟨_,
      Submodule.smul_mem _ (∏ τ, (atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ).det ^ shiftOf lam τ)
        (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.complex_span_block_action_stable lam (atInf emb (((γx x)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) hP), ?_⟩)
    rw [← fnOf_mul, ← e]
    funext z
    simp only [fnOf, Frames.tr, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.mul_one, Matrix.one_mul]
  · funext c z
    have := key (y c) c 1 (one_mem _) 1 (by simp) z z fun τ => by rw [atInf_one, Matrix.one_mul]
    rw [map_one, Units.val_one, one_mul] at this
    exact this

end Ext

section Cls

variable {X : Fields} (hc : CMData X.F X.E) {n : ℕ} [NeZero n] {SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}
  (Λ : LevFam X.E X.K n SG) (Θ : LevQFam X.E X.K n Q) (pref : DecoF X.E n ∅ SG Q → Prop) (σ : X.K →+* ℂ)

local notation "ιA" => inclE (F := X.F) (FiniteAdeleRing (𝓞 X.F) X.F)

abbrev stp : GStep X.E X.K n := stepY ∅ (Ys.triv X n) Unit (fun _ => Λ) (fun _ => Θ) pref

omit [NeZero n] in
/- English proof (translation)
The claim follows from `(toGLm X.E n).apply_symm_apply γ.1`.
-/
theorem ufGL_ratHom (γ : URat hc n) : ufGL X.E n (ratHom hc n γ) = γ.1 :=
  (toGLm X.E n).apply_symm_apply γ.1

omit [NeZero n] in
/- English proof (translation)
Take `⟨γ, rfl⟩` from `(ratHom_bijective hc n).2 g`. Rewrite using `[ufGL_ratHom]`. Conclude with `γ.2`.
-/
theorem ufGL_mem (g : UF X.E n) : ufGL X.E n g ∈ URat hc n := by
  obtain ⟨γ, rfl⟩ := (ratHom_bijective hc n).2 g
  rw [ufGL_ratHom]
  exact γ.2

/- English proof (translation)
The claim follows from `Subtype.ext ((rlc_decoOf_val hc n ∅ SG h.uni).trans (ColAd.near_of_isPtOf h 0).deco)`.
-/
theorem decoOf_eq {g : GL (Fin n) (AfE X.F X.E)} {p : DecoF X.E n ∅ SG Q} (h : IsPtOf hc g p) : decoOf ∅ SG g = p.deco :=
  Subtype.ext ((rlc_decoOf_val hc n ∅ SG h.uni).trans (ColAd.near_of_isPtOf h 0).deco)

def lev (f : ℕ) : StepLevel X.F X.E hc.sig (1 : Matrix (Fin n) (Fin n) X.E) 1 f (plUnder X.F SG) :=
  stepOf hc n (ST := ∅) (π := 1) (fun w => (Λ w).H) ⟨by simp, isCoprime_one_left⟩ (by simp)
    (fun P => iff_of_false (Finset.notMem_empty _) (one_notMem P)) (by simp)
    (fun v h => absurd (by simpa using h) (one_notMem v))
    ((baseLb_index hc n ∅ fun P => absurd P.2 (Finset.notMem_empty _)).trans (by simp))
    ((Units.map σ.toMonoidHom).comp Λ.chr)

omit [NeZero n] in
/- English proof (translation)
Unfold `Deco.L`. Rewrite using `[show {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 X.E))), d.f P x = 0} = (d.N : Set _) from Set.ext fun x => and_iff_left fun P => absurd P.2 (Finset.notMem_empty _), Submodule.span_eq]`.
-/
theorem L_empty (d : Deco X.E n ∅ SG) : d.L = d.N := by
  unfold Deco.L
  rw [show {x | x ∈ d.N ∧ ∀ P : (∅ : Finset (HeightOneSpectrum (𝓞 X.E))), d.f P x = 0} = (d.N : Set _) from
    Set.ext fun x => and_iff_left fun P => absurd P.2 (Finset.notMem_empty _), Submodule.span_eq]

omit [NeZero n] in
/- English proof (translation)
Unfold `Deco.Lsh`. Rewrite using `[L_empty]`. Conclude with `d.2.uni`.
-/
theorem Lsh_empty (d : DecoSet X.E n ∅ SG) : d.1.Lsh = d.1.N := by
  unfold Deco.Lsh
  rw [L_empty]
  exact d.2.uni

set_option maxHeartbeats 4000000 in

/- English proof (translation)
Substitute `hQ hJ hb` using the available equality. Establish `hΘ : ∀ _ : Unit, Θ = LevQFam.top X.E X.K n ∅` using `fun _ => funext fun P => absurd P.2 (Finset.notMem_empty _)`. Establish `hLb : baseLb X.E n ∅ = stdLat X.E n` using `L_empty _`. Use `choose y hy using fun c : (stp Λ Θ pref).Cl => PtExist.exists_isPtOf_cm hc n ∅ SG ∅ ((stp Λ Θ pref).rep c).1.1 (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) (by simpa using hs)`. Set `Y : (stp Λ Θ pref).Cl → UAd hc n` to `fun c => ⟨y c, (hy c).uni⟩`.

Establish `hd : ∀ c, decoOf ∅ SG (Y c).1 = ((stp Λ Θ pref).rep c).1.1.deco` using `fun c => decoOf_eq hc (hy c)`. Establish `lift : ∀ c (q : (stp Λ Θ pref).D c.1) (g₀ : UF X.E n × Λ.grp), g₀ • ((stp Λ Θ pref).rep c).1.1.deco = q.1.1.deco → ∃ g : (stp Λ Θ pref).G c.1, (g.1, g.2.1) = g₀ ∧ (stp Λ Θ pref).act c.1 g ((stp Λ Θ pref).rep c) = q` using `fun c q g₀ h => StepZero.exists_lift pref (fun _ => rfl) (fun _ => rfl) hΘ c.1 _ q g₀ h`. Establish `orb : ∀ c (x : GL (Fin n) (AfE X.F X.E)) (hx : x ∈ UAd hc n) (κ : (stp Λ Θ pref).G c.1), decoOf ∅ SG x = ((stp Λ Θ pref).act c.1 κ ((stp Λ Θ pref).rep c)).1.1.deco → ∃ k : levU hc n ∅ SG Λ.grp, Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k = κ.2.1 ∧ x = bc ιA (ufGL X.E n κ.1) * y c * …`. Introduce `c x hx κ h`. Take `⟨γ, k, h1, h2, h3⟩` from `rlc_rel_of_orbit hc n ∅ SG Λ.grp (x := ⟨x, hx⟩) (y := Y c) (κ.1, κ.2.1) (by rw [h, hd]; exact StepZero.deco_smul pref (fun _ => rfl) c.1 κ _)`.

Use `⟨k, h2, ?_⟩` and prove the remaining obligations. Establish `e : ufGL X.E n κ.1 = γ.1` using `by rw [← show ratHom hc n γ = κ.1 from h1, ufGL_ratHom]`. Rewrite using `[e]`. Conclude with `h3`. Establish `hchi : ∀ (x : (lev hc Λ σ f).U) (k : levU hc n ∅ SG Λ.grp) b (κ : (stp Λ Θ pref).G b), Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k = κ.2.1 → x.1 = k.1⁻¹ → (((lev hc Λ σ f).chi x : ℂˣ) : ℂ) = σ (((stp Λ Θ pref).chr b κ : X.Kˣ) : X.K)`.

Introduce `x k b κ h1 h2`. Take `rfl : x = (k⁻¹ : levU hc n ∅ SG Λ.grp)` from `Subtype.ext h2`. Use `show (((Units.map σ.toMonoidHom (Λ.chr (Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k⁻¹)))⁻¹ : ℂˣ) : ℂ) = σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K)`. Rewrite using `[StepZero.chr_eq_one (hΘ ()), mul_one, map_inv, map_inv, map_inv, inv_inv, h1]`. Both sides reduce to the same expression.

Set `st : ∀ c, (stp Λ Θ pref).Stab c →* UJ (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E)` to `fun c => (((stp Λ Θ pref).gam c.1).comp (Subgroup.subtype _)).codRestrict _ fun s => ufGL_mem hc s.1.1`. Establish `sm` using `rlc_decoOf_sm hc n ∅ SG Λ.grp`. Establish `hinj : Function.Injective (ufGL X.E n)` using `fun a b h => Subtype.ext ((toGLm X.E n).injective h)`. Use `⟨lev hc Λ σ f, ⟨Y, ?_, fun c x => ?_, st, fun c => ?_, fun c γ hγ => ?_, fun c s x => ?_⟩, fun x => by rw [← hLb]; rfl, hy, fun c x q hq => ?_, fun c x κ h1 h2 => ?_, fun _ _ => rfl, fun c s κ h => ?_⟩` and prove the remaining obligations. Establish `h1` using `StepZero.clMap_bijective (ST := ∅) (y := Ys.triv X n) (Λ := fun _ : Unit => Λ) (Θ := fun _ => Θ) pref (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (fun _ => rfl) (fun _ => rfl) hΘ`.

Establish `h2 : Function.Bijective (adToCls hc n ∅ SG Λ.grp ∘ fun c => (Quotient.mk'' (Y c) : AdCl hc n ∅ SG Λ.grp))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `c`. Use `show adToCls hc n ∅ SG Λ.grp (Quotient.mk'' (Y c)) = _`. Rewrite using `[adToCls_mk, hd]`.

Both sides reduce to the same expression. Conclude with `⟨h2.1.of_comp, fun a => by`. Take `⟨c, e⟩` from `h2.2 (adToCls hc n ∅ SG Λ.grp a)`. Conclude with `⟨c, adToCls_injective hc n ∅ SG Λ.grp e⟩⟩`. Use `(hy c).lat x` as an intermediate fact.

Rewrite `this` using `[← hLb]`. Conclude with `this`. Rewrite using `[injective_iff_map_eq_one]`. Introduce `s h`. Establish `h1 : s.1.1 = 1` using `hinj ((congrArg Subtype.val h).trans (map_one _).symm)`.

Establish `h2 : stabRat hc n ∅ SG Λ.grp ((stp Λ Θ pref).rep c).1.1.deco ⟨(s.1.1, s.1.2.1), (StepZero.deco_smul pref (fun _ => rfl) c.1 s.1 _).symm.trans (congrArg (fun q => q.1.1.deco) s.2)⟩ = 1`. Apply `(ratHom_bijective hc n).1` to reduce the goal to its premises. Rewrite using `[rlc_ratHom_stabRat, map_one]`. Conclude with `h1`. Establish `h3` using `(injective_iff_map_eq_one _).1 (stabRat_injective hc n ∅ SG Λ.grp _) _ h2`.

Use `Subtype.ext (Prod.ext h1 (Prod.ext (congrArg (fun a => a.1.2) h3) (Subtype.ext (funext fun P => ?_))))` and prove the remaining obligations. Conclude with `absurd P.2 (Finset.notMem_empty _)`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, e⟩`. Take `⟨k, -, h2⟩` from `orb c (y c) (hy c).uni s.1 ((hd c).trans (congrArg (fun q => q.1.1.deco) s.2).symm)`.

Use `⟨k.1, k.2, ?_⟩` and prove the remaining obligations. Establish `e' : ufGL X.E n s.1.1 = γ` using `congrArg Subtype.val e`. Rewrite `h2` using `[e']`. Use `show y c * k.1 * (y c)⁻¹ = _`. Establish `h3 : y c = bc ιA γ * y c * k.1⁻¹` using `h2`.

Rewrite using `[mul_inv_eq_iff_eq_mul, ← eq_mul_inv_iff_mul_eq]`. Conclude with `h3`. Introduce and unpack `⟨k, hk, e⟩`. Establish `e' : y c * k * (y c)⁻¹ = bc ιA γ` using `e`. Establish `h1` using `sm ⟨γ, hγ⟩ ⟨k, hk⟩ (Y c)`.

Establish `h2 : bc (iA X.F X.E) γ * (Y c).1 * k⁻¹ = (Y c).1` using `by show bc ιA γ * y c * k⁻¹ = y c`. Rewrite using `[← e']`. Use `group`. Rewrite `h1` using `[show bc (iA X.F X.E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) X.E) * (Y c).1 * (((⟨k, hk⟩ : levU hc n ∅ SG Λ.grp) : GL (Fin n) (AfE X.F X.E)))⁻¹ = (Y c).1 from h2, hd]`. Take `⟨g, h3, h4⟩` from `lift c _ _ h1.symm`.

Use `⟨⟨g, h4⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show ufGL X.E n g.1 = γ`. Rewrite using `[show g.1 = ratHom hc n ⟨γ, hγ⟩ from congrArg Prod.fst h3, ufGL_ratHom]`. Establish `h1 : gmap s.1.1.1 ((stp Λ Θ pref).rep c).1.1.deco.1.N = ((stp Λ Θ pref).rep c).1.1.deco.1.N` using `congrArg (fun q => q.1.1.deco.1.N) s.2`. Take `⟨γ, hγ⟩` from `(ratHom_bijective hc n).2 s.1.1`.

Establish `h2 : ((st c s : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x = s.1.1.1 x` using `by show ((ufGL X.E n s.1.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x = _`. Rewrite using `[← hγ, ufGL_ratHom, rlc_ratHom_apply]`. Rewrite using `[h2]`. Use `conv_rhs => rw [← h1]`. Conclude with `(Submodule.mem_map_equiv _ (e := s.1.1.1.restrictScalars (𝓞 X.E))).trans (by simp) |>.symm`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `h1` using `sm 1 ⟨x⁻¹, inv_mem hx⟩ (Y c)`. Rewrite `h1` using `[show bc (iA X.F X.E) ((1 : URat hc n) : GL (Fin n) X.E) * (Y c).1 * (((⟨x⁻¹, inv_mem hx⟩ : levU hc n ∅ SG Λ.grp) : GL (Fin n) (AfE X.F X.E)))⁻¹ = (Y c).1 * x by simp, hd, decoOf_eq hc hq]`. Take `⟨g, h3, h4⟩` from `lift c (trivPt X n ∅ SG ∅ q) _ h1.symm`.

Use `⟨g, ?_, congrArg (fun q => q.1.1) h4⟩` and prove the remaining obligations. Use `show ufGL X.E n g.1 = 1`. Rewrite using `[show g.1 = ratHom hc n 1 from congrArg Prod.fst h3, map_one, map_one]`. Introduce and unpack `⟨κ, h1, rfl⟩`. Take `⟨k, -, h2⟩` from `orb c (y c * x) hq.uni κ (decoOf_eq hc hq)`.

Establish `h5 : ufGL X.E n κ.1 = 1` using `h1`. Establish `h6 : y c * x = y c * k.1⁻¹` using `h2.trans (by rw [h5, map_one, one_mul])`. Rewrite using `[show x = k.1⁻¹ from mul_left_cancel h6]`. Conclude with `inv_mem k.2`. Take `⟨k, h3, h4⟩` from `orb c (y c * x.1) h2.uni κ (decoOf_eq hc h2)`.

Establish `h5 : ufGL X.E n κ.1 = 1` using `h1`. Establish `h6 : y c * x.1 = y c * k.1⁻¹` using `h4.trans (by rw [h5, map_one, one_mul])`. Conclude with `hchi x k _ κ h3 (mul_left_cancel h6)`. Take `⟨k, h3, h4⟩` from `orb c (y c) (hy c).uni s.1 ((hd c).trans (congrArg (fun q => q.1.1.deco) s.2).symm)`. Conclude with `hchi κ k _ s.1 h3 (mul_left_cancel (h.symm.trans h4))`.
-/
theorem exists_cls (hQ : Q = ∅) (hs : ∀ P ∈ uSG SG ∅, conjPrime₂ P ∉ uSG SG ∅) (f : ℕ) (J : Matrix (Fin n) (Fin n) X.E) (hJ : J = 1)
    (bad : Set (HeightOneSpectrum (𝓞 X.F))) (hb : bad = plUnder X.F SG) :
    ∃ (L : StepLevel X.F X.E hc.sig J 1 f bad)
      (R : RecCls hc J L.Lb L.U (stp Λ Θ pref).Stab fun c => ((stp Λ Θ pref).rep c).1.1.deco.1.N),
      (∀ x, x ∈ L.Lb ↔ x ∈ stdLat X.E n) ∧ (∀ c, IsPtOf hc (R.y c).1 ((stp Λ Θ pref).rep c).1.1) ∧
      (∀ c (x : GL (Fin n) (AfE X.F X.E)) (q : DecoF X.E n ∅ SG Q), IsPtOf hc ((R.y c).1 * x) q →
        (x ∈ L.U ↔ ∃ κ : (stp Λ Θ pref).G c.1, (stp Λ Θ pref).gam c.1 κ = 1 ∧
          ((stp Λ Θ pref).act c.1 κ ((stp Λ Θ pref).rep c)).1.1 = q)) ∧
      (∀ c (x : L.U) (κ : (stp Λ Θ pref).G c.1), (stp Λ Θ pref).gam c.1 κ = 1 →
        IsPtOf hc ((R.y c).1 * x.1) ((stp Λ Θ pref).act c.1 κ ((stp Λ Θ pref).rep c)).1.1 →
        ((L.chi x : ℂˣ) : ℂ) = σ (((stp Λ Θ pref).chr c.1 κ : X.Kˣ) : X.K)) ∧
      (∀ c s, (R.stabI c s).1 = (stp Λ Θ pref).gam c.1 s.1) ∧
      ∀ c (s : (stp Λ Θ pref).Stab c) (κ : L.U), (R.y c).1 = bc ιA (R.stabI c s).1 * (R.y c).1 * κ.1 →
        ((L.chi κ : ℂˣ) : ℂ) = σ (((stp Λ Θ pref).chr c.1 s.1 : X.Kˣ) : X.K) := by
  classical
  subst hQ hJ hb
  have hΘ : ∀ _ : Unit, Θ = LevQFam.top X.E X.K n ∅ := fun _ => funext fun P => absurd P.2 (Finset.notMem_empty _)
  have hLb : baseLb X.E n ∅ = stdLat X.E n := L_empty _
  choose y hy using fun c : (stp Λ Θ pref).Cl => PtExist.exists_isPtOf_cm hc n ∅ SG ∅ ((stp Λ Θ pref).rep c).1.1
    (Finset.disjoint_empty_left _) (Finset.disjoint_empty_left _) (Finset.disjoint_empty_right _) (by simpa using hs)
  let Y : (stp Λ Θ pref).Cl → UAd hc n := fun c => ⟨y c, (hy c).uni⟩
  have hd : ∀ c, decoOf ∅ SG (Y c).1 = ((stp Λ Θ pref).rep c).1.1.deco := fun c => decoOf_eq hc (hy c)
  have lift : ∀ c (q : (stp Λ Θ pref).D c.1) (g₀ : UF X.E n × Λ.grp), g₀ • ((stp Λ Θ pref).rep c).1.1.deco = q.1.1.deco →
      ∃ g : (stp Λ Θ pref).G c.1, (g.1, g.2.1) = g₀ ∧ (stp Λ Θ pref).act c.1 g ((stp Λ Θ pref).rep c) = q :=
    fun c q g₀ h => StepZero.exists_lift pref (fun _ => rfl) (fun _ => rfl) hΘ c.1 _ q g₀ h
  have orb : ∀ c (x : GL (Fin n) (AfE X.F X.E)) (hx : x ∈ UAd hc n) (κ : (stp Λ Θ pref).G c.1),
      decoOf ∅ SG x = ((stp Λ Θ pref).act c.1 κ ((stp Λ Θ pref).rep c)).1.1.deco →
      ∃ k : levU hc n ∅ SG Λ.grp, Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k = κ.2.1 ∧ x = bc ιA (ufGL X.E n κ.1) * y c * k.1⁻¹ := by
    intro c x hx κ h
    obtain ⟨γ, k, h1, h2, h3⟩ := rlc_rel_of_orbit hc n ∅ SG Λ.grp (x := ⟨x, hx⟩) (y := Y c) (κ.1, κ.2.1)
      (by rw [h, hd]; exact StepZero.deco_smul pref (fun _ => rfl) c.1 κ _)
    refine ⟨k, h2, ?_⟩
    have e : ufGL X.E n κ.1 = γ.1 := by rw [← show ratHom hc n γ = κ.1 from h1, ufGL_ratHom]
    rw [e]
    exact h3
  have hchi : ∀ (x : (lev hc Λ σ f).U) (k : levU hc n ∅ SG Λ.grp) b (κ : (stp Λ Θ pref).G b), Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k = κ.2.1 → x.1 = k.1⁻¹ →
      (((lev hc Λ σ f).chi x : ℂˣ) : ℂ) = σ (((stp Λ Θ pref).chr b κ : X.Kˣ) : X.K) := by
    intro x k b κ h1 h2
    obtain rfl : x = (k⁻¹ : levU hc n ∅ SG Λ.grp) := Subtype.ext h2
    show (((Units.map σ.toMonoidHom (Λ.chr (Formalism.L2.Col.levRed hc n ∅ SG Λ.grp k⁻¹)))⁻¹ : ℂˣ) : ℂ) =
      σ ((Λ.chr κ.2.1 * Θ.chr κ.2.2 : X.Kˣ) : X.K)
    rw [StepZero.chr_eq_one (hΘ ()), mul_one, map_inv, map_inv, map_inv, inv_inv, h1]
    rfl
  let st : ∀ c, (stp Λ Θ pref).Stab c →* UJ (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) := fun c =>
    (((stp Λ Θ pref).gam c.1).comp (Subgroup.subtype _)).codRestrict _ fun s => ufGL_mem hc s.1.1
  have sm := rlc_decoOf_sm hc n ∅ SG Λ.grp
  have hinj : Function.Injective (ufGL X.E n) := fun a b h => Subtype.ext ((toGLm X.E n).injective h)
  refine ⟨lev hc Λ σ f, ⟨Y, ?_, fun c x => ?_, st, fun c => ?_, fun c γ hγ => ?_, fun c s x => ?_⟩,
    fun x => by rw [← hLb]; rfl, hy, fun c x q hq => ?_, fun c x κ h1 h2 => ?_, fun _ _ => rfl, fun c s κ h => ?_⟩
  · have h1 := StepZero.clMap_bijective (ST := ∅) (y := Ys.triv X n) (Λ := fun _ : Unit => Λ) (Θ := fun _ => Θ) pref
      (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩) (fun _ => rfl) (fun _ => rfl) hΘ
    have h2 : Function.Bijective (adToCls hc n ∅ SG Λ.grp ∘ fun c => (Quotient.mk'' (Y c) : AdCl hc n ∅ SG Λ.grp)) := by
      convert h1 using 1
      funext c
      show adToCls hc n ∅ SG Λ.grp (Quotient.mk'' (Y c)) = _
      rw [adToCls_mk, hd]
      rfl
    exact ⟨h2.1.of_comp, fun a => by
      obtain ⟨c, e⟩ := h2.2 (adToCls hc n ∅ SG Λ.grp a)
      exact ⟨c, adToCls_injective hc n ∅ SG Λ.grp e⟩⟩
  · have := (hy c).lat x
    rw [← hLb] at this
    exact this
  · rw [injective_iff_map_eq_one]
    intro s h
    have h1 : s.1.1 = 1 := hinj ((congrArg Subtype.val h).trans (map_one _).symm)
    have h2 : stabRat hc n ∅ SG Λ.grp ((stp Λ Θ pref).rep c).1.1.deco
        ⟨(s.1.1, s.1.2.1), (StepZero.deco_smul pref (fun _ => rfl) c.1 s.1 _).symm.trans (congrArg (fun q => q.1.1.deco) s.2)⟩ = 1 := by
      apply (ratHom_bijective hc n).1
      rw [rlc_ratHom_stabRat, map_one]
      exact h1
    have h3 := (injective_iff_map_eq_one _).1 (stabRat_injective hc n ∅ SG Λ.grp _) _ h2
    refine Subtype.ext (Prod.ext h1 (Prod.ext (congrArg (fun a => a.1.2) h3) (Subtype.ext (funext fun P => ?_))))
    exact absurd P.2 (Finset.notMem_empty _)
  · constructor
    · rintro ⟨s, e⟩
      obtain ⟨k, -, h2⟩ := orb c (y c) (hy c).uni s.1 ((hd c).trans (congrArg (fun q => q.1.1.deco) s.2).symm)
      refine ⟨k.1, k.2, ?_⟩
      have e' : ufGL X.E n s.1.1 = γ := congrArg Subtype.val e
      rw [e'] at h2
      show y c * k.1 * (y c)⁻¹ = _
      have h3 : y c = bc ιA γ * y c * k.1⁻¹ := h2
      rw [mul_inv_eq_iff_eq_mul, ← eq_mul_inv_iff_mul_eq]
      exact h3
    · rintro ⟨k, hk, e⟩
      have e' : y c * k * (y c)⁻¹ = bc ιA γ := e
      have h1 := sm ⟨γ, hγ⟩ ⟨k, hk⟩ (Y c)
      have h2 : bc (iA X.F X.E) γ * (Y c).1 * k⁻¹ = (Y c).1 := by
        show bc ιA γ * y c * k⁻¹ = y c
        rw [← e']
        group
      rw [show bc (iA X.F X.E) ((⟨γ, hγ⟩ : URat hc n) : GL (Fin n) X.E) * (Y c).1 *
        (((⟨k, hk⟩ : levU hc n ∅ SG Λ.grp) : GL (Fin n) (AfE X.F X.E)))⁻¹ = (Y c).1 from h2, hd] at h1
      obtain ⟨g, h3, h4⟩ := lift c _ _ h1.symm
      refine ⟨⟨g, h4⟩, Subtype.ext ?_⟩
      show ufGL X.E n g.1 = γ
      rw [show g.1 = ratHom hc n ⟨γ, hγ⟩ from congrArg Prod.fst h3, ufGL_ratHom]
  · have h1 : gmap s.1.1.1 ((stp Λ Θ pref).rep c).1.1.deco.1.N = ((stp Λ Θ pref).rep c).1.1.deco.1.N :=
      congrArg (fun q => q.1.1.deco.1.N) s.2
    obtain ⟨γ, hγ⟩ := (ratHom_bijective hc n).2 s.1.1
    have h2 : ((st c s : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x = s.1.1.1 x := by
      show ((ufGL X.E n s.1.1 : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) *ᵥ x = _
      rw [← hγ, ufGL_ratHom, rlc_ratHom_apply]
    rw [h2]
    conv_rhs => rw [← h1]
    exact (Submodule.mem_map_equiv _ (e := s.1.1.1.restrictScalars (𝓞 X.E))).trans (by simp) |>.symm
  · constructor
    · intro hx
      have h1 := sm 1 ⟨x⁻¹, inv_mem hx⟩ (Y c)
      rw [show bc (iA X.F X.E) ((1 : URat hc n) : GL (Fin n) X.E) * (Y c).1 *
        (((⟨x⁻¹, inv_mem hx⟩ : levU hc n ∅ SG Λ.grp) : GL (Fin n) (AfE X.F X.E)))⁻¹ = (Y c).1 * x by simp, hd,
        decoOf_eq hc hq] at h1
      obtain ⟨g, h3, h4⟩ := lift c (trivPt X n ∅ SG ∅ q) _ h1.symm
      refine ⟨g, ?_, congrArg (fun q => q.1.1) h4⟩
      show ufGL X.E n g.1 = 1
      rw [show g.1 = ratHom hc n 1 from congrArg Prod.fst h3, map_one, map_one]
    · rintro ⟨κ, h1, rfl⟩
      obtain ⟨k, -, h2⟩ := orb c (y c * x) hq.uni κ (decoOf_eq hc hq)
      have h5 : ufGL X.E n κ.1 = 1 := h1
      have h6 : y c * x = y c * k.1⁻¹ := h2.trans (by rw [h5, map_one, one_mul])
      rw [show x = k.1⁻¹ from mul_left_cancel h6]
      exact inv_mem k.2
  · obtain ⟨k, h3, h4⟩ := orb c (y c * x.1) h2.uni κ (decoOf_eq hc h2)
    have h5 : ufGL X.E n κ.1 = 1 := h1
    have h6 : y c * x.1 = y c * k.1⁻¹ := h4.trans (by rw [h5, map_one, one_mul])
    exact hchi x k _ κ h3 (mul_left_cancel h6)
  · obtain ⟨k, h3, h4⟩ := orb c (y c) (hy c).uni s.1 ((hd c).trans (congrArg (fun q => q.1.1.deco) s.2).symm)
    exact hchi κ k _ s.1 h3 (mul_left_cancel (h.symm.trans h4))

end Cls

end GlobalTheory.Mem.Col2.RowTie

end
