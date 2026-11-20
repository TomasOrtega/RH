import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OneBlockPnPt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.MemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockEqChartRing
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPointDegreePos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mConeMapOver mIdealOver chartRingOver)

noncomputable section

section Units

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `ha`. Conclude with `⟨coe_ne_zero_of_not_mem ha, mem_locIn.mpr ⟨1, a, ha, by simp⟩⟩`. Introduce and unpack `⟨h0, hinv⟩ ha`. Take `⟨a', b', hb', he⟩` from `mem_locIn.mp hinv`.

Establish `hb0` using `coe_ne_zero_of_not_mem hb'`. Apply `hb'` to reduce the goal to its premises. Establish `hba : b' = a * a'`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite `he` using `[eq_div_iff hb0]`.

Use `push_cast`. Rewrite using `[← he, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]`. Rewrite using `[hba]`. Conclude with `p.mul_mem_right _ ha`.
-/
theorem not_mem_iff_unit_locIn {A : Subalgebra S Ω} {p : Ideal A} [hp : p.IsPrime] (a : A) :
    a ∉ p ↔ (a : Ω) ≠ 0 ∧ (a : Ω)⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
  constructor
  · intro ha
    exact ⟨coe_ne_zero_of_not_mem ha, mem_locIn.mpr ⟨1, a, ha, by simp⟩⟩
  · rintro ⟨h0, hinv⟩ ha
    obtain ⟨a', b', hb', he⟩ := mem_locIn.mp hinv
    have hb0 := coe_ne_zero_of_not_mem hb'
    apply hb'
    have hba : b' = a * a' := by
      apply Subtype.ext
      rw [eq_div_iff hb0] at he
      push_cast
      rw [← he, ← mul_assoc, mul_inv_cancel₀ h0, one_mul]
    rw [hba]
    exact p.mul_mem_right _ ha

/- English proof (translation)
Establish `htd : t ^ d ∈ R` using `pow_mem ht d`. Establish `htdi : (t ^ d)⁻¹ ∈ R` using `by rw [← inv_pow]; exact pow_mem hti d`. Establish `htd0 : t ^ d ≠ 0` using `pow_ne_zero d ht0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, hi⟩`.

Use `⟨left_ne_zero_of_mul h0, ?_⟩` and prove the remaining obligations. Establish `hu : u⁻¹ = (u * t ^ d)⁻¹ * t ^ d` using `by rw [mul_inv, mul_assoc, inv_mul_cancel₀ htd0, mul_one]`. Rewrite using `[hu]`. Conclude with `mul_mem hi htd`. Introduce and unpack `⟨h0, hi⟩`.

Use `⟨mul_ne_zero h0 htd0, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_inv]`. Conclude with `mul_mem hi htdi`.
-/
theorem unit_mul_pow_iff {R : Subring Ω} {t : Ω} (ht : t ∈ R) (ht0 : t ≠ 0) (hti : t⁻¹ ∈ R) (u : Ω) (d : ℕ) :
    (u * t ^ d ≠ 0 ∧ (u * t ^ d)⁻¹ ∈ R) ↔ (u ≠ 0 ∧ u⁻¹ ∈ R) := by
  have htd : t ^ d ∈ R := pow_mem ht d
  have htdi : (t ^ d)⁻¹ ∈ R := by rw [← inv_pow]; exact pow_mem hti d
  have htd0 : t ^ d ≠ 0 := pow_ne_zero d ht0
  constructor
  · rintro ⟨h0, hi⟩
    refine ⟨left_ne_zero_of_mul h0, ?_⟩
    have hu : u⁻¹ = (u * t ^ d)⁻¹ * t ^ d := by rw [mul_inv, mul_assoc, inv_mul_cancel₀ htd0, mul_one]
    rw [hu]
    exact mul_mem hi htd
  · rintro ⟨h0, hi⟩
    refine ⟨mul_ne_zero h0 htd0, ?_⟩
    rw [mul_inv]
    exact mul_mem hi htdi

end Units

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.Kleiman2.residue`. Rewrite using `[dif_pos a.2]`.
-/
theorem residue_coe {F : Type} [Field F] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω] [Algebra F Ω]
    {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} {p : Ideal (chartRingOver F y c)} [p.IsPrime] (a : chartRingOver F y c) :
    IndefiniteRowSideFullHecke.Kleiman2.residue F y c p (a : Ω) =
      algebraMap (chartRingOver F y c ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p) (Ideal.Quotient.mk p a) := by
  unfold IndefiniteRowSideFullHecke.Kleiman2.residue
  rw [dif_pos a.2]

/- English proof (translation)
Establish `hcomp : ((Polynomial.aeval (X () : MvPolynomial Unit Ω')).restrictScalars S).comp ((Kleiman.cone (S` using `S) z).comp (Kleiman.oneBlock (S := S) (N := N))) = mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock z) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨⟨⟩, i⟩`. Simplify using `[mConeMapOver, Kleiman.cone_eq, Kleiman.coneGen, Kleiman.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]`. Establish `hinj : Function.Injective (Polynomial.aeval (R` using `Ω') (X () : MvPolynomial Unit Ω')) := by`.

Establish `hid : (aeval (fun _ : Unit => (Polynomial.X : Polynomial Ω'))).comp (Polynomial.aeval (R` using `Ω') (X () : MvPolynomial Unit Ω')) = AlgHom.id Ω' (Polynomial Ω') := Polynomial.algHom_ext (by simp)`. Conclude with `Function.LeftInverse.injective (g := aeval (fun _ : Unit => (Polynomial.X : Polynomial Ω'))) fun q => by`. Establish `h` using `AlgHom.congr_fun hid q`. Rewrite `h` using `[AlgHom.comp_apply, AlgHom.id_apply]`. Then use the resulting hypothesis. Use extensionality with `f`.

Rewrite using `[Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock z) f = 0 ↔ _`. Rewrite using `[← hcomp, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_eq_zero_iff _ hinj, AlgHom.comp_apply]`.
-/
theorem mIdealOver_oneBlock_eq {S : Type} [CommRing S] {Ω' : Type} [Field Ω'] [Algebra S Ω'] {N : ℕ}
    (z : Fin (N + 1) → Ω') :
    mIdealOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock z) =
      (Kleiman.primeOf (S := S) z).comap (Kleiman.oneBlock (S := S) (N := N)) := by
  have hcomp : ((Polynomial.aeval (X () : MvPolynomial Unit Ω')).restrictScalars S).comp
      ((Kleiman.cone (S := S) z).comp (Kleiman.oneBlock (S := S) (N := N))) =
        mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock z) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨⟨⟩, i⟩
    simp [mConeMapOver, Kleiman.cone_eq, Kleiman.coneGen, Kleiman.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.oneBlock]
  have hinj : Function.Injective (Polynomial.aeval (R := Ω') (X () : MvPolynomial Unit Ω')) := by
    have hid : (aeval (fun _ : Unit => (Polynomial.X : Polynomial Ω'))).comp
        (Polynomial.aeval (R := Ω') (X () : MvPolynomial Unit Ω')) = AlgHom.id Ω' (Polynomial Ω') :=
      Polynomial.algHom_ext (by simp)
    exact Function.LeftInverse.injective (g := aeval (fun _ : Unit => (Polynomial.X : Polynomial Ω'))) fun q => by
      have h := AlgHom.congr_fun hid q
      rwa [AlgHom.comp_apply, AlgHom.id_apply] at h
  ext f
  rw [Ideal.mem_comap, Kleiman.primeOf_eq, RingHom.mem_ker]
  change mConeMapOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock z) f = 0 ↔ _
  rw [← hcomp, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_eq_zero_iff _ hinj, AlgHom.comp_apply]

/- English proof (translation)
Establish `hcomp : (mConeMapOver F w).comp (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) = ((rename (R` using `Ω') fun _ : Unit => k₀).restrictScalars F).comp (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec w k₀ ∘ e.symm))) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Simplify using `[mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]`. Establish `hinj : Function.Injective (rename (R` using `Ω') fun _ : Unit => k₀) := rename_injective _ fun a b _ => Subsingleton.elim a b`.

Use extensionality with `f`. Rewrite using `[baseComap, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `mConeMapOver F w (rename _ f) = 0 ↔ mConeMapOver F _ f = 0`. Rewrite using `[← AlgHom.comp_apply, hcomp, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_eq_zero_iff _ hinj]`.
-/
theorem baseComap_mIdealOver (F : Type) [Field F] {K : Type} {ι : K → Type} {Ω' : Type} [Field Ω'] [Algebra F Ω']
    (w : (Σ k, ι k) → Ω') (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) :
    baseComap F k₀ e (mIdealOver F w) =
      mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec w k₀ ∘ e.symm)) := by
  have hcomp : (mConeMapOver F w).comp
      (rename fun p : (Σ _ : Unit, Fin (N + 1)) => (⟨k₀, e.symm p.2⟩ : Σ k, ι k)) =
      ((rename (R := Ω') fun _ : Unit => k₀).restrictScalars F).comp
        (mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec w k₀ ∘ e.symm))) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
  have hinj : Function.Injective (rename (R := Ω') fun _ : Unit => k₀) :=
    rename_injective _ fun a b _ => Subsingleton.elim a b
  ext f
  rw [baseComap, Ideal.mem_comap]
  change mConeMapOver F w (rename _ f) = 0 ↔ mConeMapOver F _ f = 0
  rw [← AlgHom.comp_apply, hcomp, AlgHom.comp_apply, AlgHom.restrictScalars_apply, map_eq_zero_iff _ hinj]

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy P hP hxP`. Use `hP.isPrime` as an intermediate fact. Establish `hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩` using `fun i => by rw [hx]; rfl`. Use `set pp : Ideal (Kleiman.Poly F N) := P.comap (renameEquiv F (HilbertPositive.blockEquiv N)).symm with hpp`. Establish `hmemP : ∀ g, Kleiman.oneBlock (S` using `F) (N := N) g ∈ pp ↔ g ∈ P := by`.

Introduce `g`. Rewrite using `[hpp, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `(renameEquiv F (HilbertPositive.blockEquiv N)).symm (renameEquiv F (HilbertPositive.blockEquiv N) g) ∈ P ↔ _`. Rewrite using `[AlgEquiv.symm_apply_apply]`. Establish `hsurj : ∀ f : Kleiman.Poly F N, ∃ g, Kleiman.oneBlock (S` using `F) (N := N) g = f := fun f => ⟨(renameEquiv F (HilbertPositive.blockEquiv N)).symm f, (renameEquiv F (HilbertPositive.blockEquiv N)).apply_symm_apply f⟩`.

Establish `hpp_prime : pp.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hpp_homog : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp`. Introduce `f hf d`. Take `⟨g, rfl⟩` from `hsurj f`. Rewrite `hf` using `[hmemP]`.

Rewrite using `[← Kleiman.oneBlock_homogeneousComponent, hmemP]`. Establish `heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) (fun _ => d) g = homogeneousComponent d g`. Use extensionality with `m`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, HilbertPositive.weight_blockWeight_one m]`. Use `congr 1`.

Apply `propext` to reduce the goal to its premises. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `congrFun h ()`. Introduce `h`.

Use function extensionality and compare the values at `u`. Conclude with `h`. Rewrite using `[← heq]`. Conclude with `hP.multiHomog g hf _`. Establish `hpp_le : Kleiman.primeOf (S` using `F) x ≤ pp := by`.

Introduce `f hf`. Take `⟨g, rfl⟩` from `hsurj f`. Rewrite using `[hmemP]`. Apply `hxP` to reduce the goal to its premises. Rewrite using `[mIdealOver_oneBlock_eq, Ideal.mem_comap]`.

Conclude with `hf`. Take `⟨j, hjP⟩` from `hP.relevant ()`. Establish `hXj : (X j : Kleiman.Poly F N) ∉ pp`. Establish `h1 : (X j : Kleiman.Poly F N) = Kleiman.oneBlock (S` using `F) (N := N) (X ⟨(), j⟩) := by`. Rewrite using `[Kleiman.oneBlock, rename_X]`.

Rewrite using `[h1, hmemP]`. Conclude with `hjP`. Establish `hj : x j ≠ 0`. Introduce `h0`. Apply `hjP` to reduce the goal to its premises.

Apply `hxP` to reduce the goal to its premises. Use `show mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (X ⟨(), j⟩) = 0`. Simplify using `[mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, h0]`. Take `⟨hcp, hpt⟩` from `Kleiman.PrimeFiltration.Point.proof F Ω N x pp hpp_prime hpp_homog hpp_le j hj hXj`. Use `hcp` as an intermediate fact.

Set `CR` to `Kleiman.chartRing F x (Kleiman.singleChart hj)`. Set `Ip : Ideal CR` to `Kleiman.chartPrime pp hj`. Set `ψ : CR →ₐ[F] Ip.ResidueField` to `IsScalarTower.toAlgHom F CR Ip.ResidueField`. Establish `hker : RingHom.ker ψ = Ip` using `Ideal.ker_algebraMap_residueField Ip`. Establish `hpy : Kleiman.primeOf (S` using `F) (fun i => ψ (Kleiman.ratio hj i)) = pp := hpt _ ψ hker`.

Set `c' : ∀ _ : Unit, ι k₀` to `fun _ => e.symm j`. Set `B` to `chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'`. Establish `hyj : y ⟨k₀, e.symm j⟩ ≠ 0` using `by rw [← hxv]; exact hj`. Establish `hBC : B ≤ CR`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨⟨⟩, b⟩, rfl⟩`. Establish `h1 : y ⟨k₀, b⟩ / y ⟨k₀, e.symm j⟩ = x (e b) / x j` using `by rw [hxv, hxv, e.symm_apply_apply]`. Use `show y ⟨k₀, b⟩ / y ⟨k₀, e.symm j⟩ ∈ CR`. Rewrite using `[h1]`. Conclude with `(Kleiman.ratio (S := F) hj (e b)).2`.

Set `q' : Ideal B` to `RingHom.ker (ψ.comp (Subalgebra.inclusion hBC))`. Establish `hq' : q'.IsPrime` using `RingHom.ker_isPrime _`. Establish `hRB : IndefiniteRowSideFullHecke.Kleiman2.locIn B q' ∈ IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))` using `⟨c', fun _ => hyj, q', hq', rfl⟩`. Rewrite `hRB` using `[← (hy.2 : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = _)]`. Take `⟨c, hc, p, hp, hRA⟩` from `hRB`.

Use `hp` as an intermediate fact. Set `A` to `chartRingOver F y c`. Set `u : (Σ k, ι k) → A` to `fun q => ⟨y q / y ⟨q.1, c q.1⟩, Algebra.subset_adjoin ⟨q, rfl⟩⟩`. Set `φ : A →ₐ[F] IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p` to `{ (algebraMap (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p)).comp (Ideal.Quotient.mk p) with commutes' := fun _ => rfl }`. Establish `hφ : ∀ a, φ a = 0 ↔ a ∈ p`.

Introduce `a`. Establish `: IsFractionRing (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p)` using `inferInstanceAs (IsFractionRing (A ⧸ p) (FractionRing (A ⧸ p)))`. Use `show algebraMap (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p) (Ideal.Quotient.mk p a) = 0 ↔ a ∈ p`. Rewrite using `[IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hmod : ∀ q, IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p q = φ (u q)`.

Introduce `q`. Use `show IndefiniteRowSideFullHecke.Kleiman2.residue F y c p ((u q : A) : Ω) = _`. Rewrite using `[residue_coe]`. Both sides reduce to the same expression. Use `⟨mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p), isMultiProjPrime_mIdealOver _ fun k => ⟨c k, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hmod]`. Establish `h1 : u ⟨k, c k⟩ = 1` using `Subtype.ext (by simp [u, div_self (hc k)])`. Rewrite using `[h1, map_one]`. Conclude with `one_ne_zero`. Introduce `f hf`.

Rewrite `hf`, the goal using `[mem_mIdealOver_iff]`. Introduce `b`. Establish `hfb` using `weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight ι) b f`. Establish `key` using `aeval_mul_block y (fun k => (y ⟨k, c k⟩)⁻¹) b _ hfb`. Rewrite `key` using `[hf b, zero_mul]`.

Establish `hu : (fun q => A.val (u q)) = fun q => y q * (fun k => (y ⟨k, c k⟩)⁻¹) q.1`. Use function extensionality and compare the values at `q`. Simplify using `[u, div_eq_mul_inv]`. Establish `h0 : aeval u (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `A.val (aeval u _) = 0`. Rewrite using `[comp_aeval_apply]`. Conclude with `(congrArg (fun v => aeval v (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f)) hu).trans key`. Establish `hw : IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p = fun q => φ (u q)` using `funext hmod`. Rewrite using `[hw, ← comp_aeval_apply, h0, map_zero]`.

Rewrite using `[baseComap_mIdealOver]`. Establish `hPx : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (fun i => ψ (Kleiman.ratio hj i))) = P`. Use extensionality with `g`. Rewrite using `[mIdealOver_oneBlock_eq, Ideal.mem_comap, hpy, hmemP]`. Rewrite using `[← hPx]`.

Use extensionality with `f`. Rewrite using `[mem_mIdealOver_iff, mem_mIdealOver_iff]`. Use `forall_congr' fun b => ?_` and prove the remaining obligations. Use `set g := weightedHomogeneousComponent (NumbersDVR.blockWeight fun _ : Unit => Fin (N + 1)) b f`. Establish `hg : IsWeightedHomogeneous (NumbersDVR.blockWeight fun _ : Unit => Fin (N + 1)) g b` using `weightedHomogeneousComponent_isWeightedHomogeneous b f`.

Set `va : (Σ _ : Unit, Fin (N + 1)) → A` to `fun v => u ⟨k₀, e.symm v.2⟩`. Set `vb : (Σ _ : Unit, Fin (N + 1)) → B` to `fun v => ⟨y ⟨k₀, e.symm v.2⟩ / y ⟨k₀, e.symm j⟩, Algebra.subset_adjoin ⟨⟨(), e.symm v.2⟩, rfl⟩⟩`. Establish `hza : aeval (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p) k₀ ∘ e.symm)) g = φ (aeval va g)`. Rewrite using `[comp_aeval_apply]`. Conclude with `congrArg (fun v => aeval v g) (funext fun v => hmod _)`.

Establish `hzb : aeval (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (fun i => ψ (Kleiman.ratio hj i))) g = (ψ.comp (Subalgebra.inclusion hBC)) (aeval vb g)`. Rewrite using `[comp_aeval_apply]`. Use `congrArg (fun v => aeval v g) (funext fun v => ?_)` and prove the remaining obligations. Use `show ψ (Kleiman.ratio hj v.2) = ψ (Subalgebra.inclusion hBC (vb v))`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show x v.2 / x j = y ⟨k₀, e.symm v.2⟩ / y ⟨k₀, e.symm j⟩`. Rewrite using `[hxv, hxv]`. Use `set t : Ω := y ⟨k₀, c k₀⟩ / y ⟨k₀, e.symm j⟩ with ht`. Establish `htB : t ∈ B` using `Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩`.

Establish `htR : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p`. Rewrite using `[← hRA]`. Conclude with `mem_locIn.mpr ⟨⟨t, htB⟩, 1, one_not_mem_of_prime hq', by simp⟩`. Establish `ht0 : t ≠ 0` using `div_ne_zero (hc k₀) hyj`. Establish `htiA : t⁻¹ ∈ A`.

Rewrite using `[ht, inv_div]`. Conclude with `Algebra.subset_adjoin ⟨⟨k₀, e.symm j⟩, rfl⟩`. Establish `hti : t⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p` using `mem_locIn.mpr ⟨⟨t⁻¹, htiA⟩, 1, one_not_mem_of_prime hp, by simp⟩`. Establish `hab : ((aeval vb g : B) : Ω) = ((aeval va g : A) : Ω) * t ^ (b ())`. Establish `key` using `aeval_mul_block (fun v : (Σ _ : Unit, Fin (N + 1)) => ((va v : A) : Ω)) (fun _ => t) b g hg`.

Establish `hv : (fun v => B.val (vb v)) = fun v => ((va v : A) : Ω) * (fun _ : Unit => t) v.1`. Use function extensionality and compare the values at `⟨⟨⟩, i⟩`. Use `show y ⟨k₀, e.symm i⟩ / y ⟨k₀, e.symm j⟩ = y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ * t`. Rewrite using `[ht]`. Clear denominators, using `[hc k₀, hyj]` for the nonvanishing conditions.

Express the relevant statement in the definitionally equal form `B.val (aeval vb g) = A.val (aeval va g) * _`. Rewrite using `[comp_aeval_apply, comp_aeval_apply]`. Use `(congrArg (fun v => aeval v g) hv).trans (key.trans ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[hza, hzb, hφ, ← RingHom.mem_ker]`.

Establish `e1` using `not_mem_iff_unit_locIn (p := p) (aeval va g)`. Establish `e2` using `not_mem_iff_unit_locIn (p := q') (aeval vb g)`. Rewrite `e2` using `[hab, hRA]`. Rewrite using `[← not_iff_not, e1]`. Express the relevant statement in the definitionally equal form `_ ↔ aeval vb g ∉ q'`.

Rewrite using `[e2, unit_mul_pow_iff htR ht0 hti]`.
-/
theorem ModelCurvesLift.proof : ModelCurvesLift.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hy P hP hxP
  classical
  have := hP.isPrime
  have hxv : ∀ i, x i = y ⟨k₀, e.symm i⟩ := fun i => by rw [hx]; rfl

  set pp : Ideal (Kleiman.Poly F N) := P.comap (renameEquiv F (HilbertPositive.blockEquiv N)).symm with hpp
  have hmemP : ∀ g, Kleiman.oneBlock (S := F) (N := N) g ∈ pp ↔ g ∈ P := by
    intro g
    rw [hpp, Ideal.mem_comap]
    change (renameEquiv F (HilbertPositive.blockEquiv N)).symm (renameEquiv F (HilbertPositive.blockEquiv N) g) ∈ P ↔ _
    rw [AlgEquiv.symm_apply_apply]
  have hsurj : ∀ f : Kleiman.Poly F N, ∃ g, Kleiman.oneBlock (S := F) (N := N) g = f := fun f =>
    ⟨(renameEquiv F (HilbertPositive.blockEquiv N)).symm f,
      (renameEquiv F (HilbertPositive.blockEquiv N)).apply_symm_apply f⟩
  have hpp_prime : pp.IsPrime := Ideal.comap_isPrime _ _
  have hpp_homog : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp := by
    intro f hf d
    obtain ⟨g, rfl⟩ := hsurj f
    rw [hmemP] at hf
    rw [← Kleiman.oneBlock_homogeneousComponent, hmemP]
    have heq : weightedHomogeneousComponent (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) (fun _ => d) g =
        homogeneousComponent d g := by
      ext m
      rw [coeff_weightedHomogeneousComponent, coeff_homogeneousComponent, HilbertPositive.weight_blockWeight_one m]
      congr 1
      apply propext
      constructor
      · intro h; exact congrFun h ()
      · intro h; funext u; exact h
    rw [← heq]
    exact hP.multiHomog g hf _
  have hpp_le : Kleiman.primeOf (S := F) x ≤ pp := by
    intro f hf
    obtain ⟨g, rfl⟩ := hsurj f
    rw [hmemP]
    apply hxP
    rw [mIdealOver_oneBlock_eq, Ideal.mem_comap]
    exact hf
  obtain ⟨j, hjP⟩ := hP.relevant ()
  have hXj : (X j : Kleiman.Poly F N) ∉ pp := by
    have h1 : (X j : Kleiman.Poly F N) = Kleiman.oneBlock (S := F) (N := N) (X ⟨(), j⟩) := by
      rw [Kleiman.oneBlock, rename_X]
    rw [h1, hmemP]
    exact hjP
  have hj : x j ≠ 0 := by
    intro h0
    apply hjP
    apply hxP
    show mConeMapOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (X ⟨(), j⟩) = 0
    simp [mConeMapOver, IndefiniteRowSideFullHecke.Kleiman2.oneBlock, h0]

  obtain ⟨hcp, hpt⟩ := Kleiman.PrimeFiltration.Point.proof F Ω N x pp hpp_prime hpp_homog hpp_le j hj hXj
  have := hcp
  let CR := Kleiman.chartRing F x (Kleiman.singleChart hj)
  let Ip : Ideal CR := Kleiman.chartPrime pp hj
  let ψ : CR →ₐ[F] Ip.ResidueField := IsScalarTower.toAlgHom F CR Ip.ResidueField
  have hker : RingHom.ker ψ = Ip := Ideal.ker_algebraMap_residueField Ip
  have hpy : Kleiman.primeOf (S := F) (fun i => ψ (Kleiman.ratio hj i)) = pp := hpt _ ψ hker

  let c' : ∀ _ : Unit, ι k₀ := fun _ => e.symm j
  let B := chartRingOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) c'
  have hyj : y ⟨k₀, e.symm j⟩ ≠ 0 := by rw [← hxv]; exact hj
  have hBC : B ≤ CR := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨⟨⟩, b⟩, rfl⟩
    have h1 : y ⟨k₀, b⟩ / y ⟨k₀, e.symm j⟩ = x (e b) / x j := by rw [hxv, hxv, e.symm_apply_apply]
    show y ⟨k₀, b⟩ / y ⟨k₀, e.symm j⟩ ∈ CR
    rw [h1]
    exact (Kleiman.ratio (S := F) hj (e b)).2
  let q' : Ideal B := RingHom.ker (ψ.comp (Subalgebra.inclusion hBC))
  have hq' : q'.IsPrime := RingHom.ker_isPrime _

  have hRB : IndefiniteRowSideFullHecke.Kleiman2.locIn B q' ∈
      IndefiniteRowSideFullHecke.Kleiman2.modelPts F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) :=
    ⟨c', fun _ => hyj, q', hq', rfl⟩
  rw [← (hy.2 : IndefiniteRowSideFullHecke.Kleiman2.modelPts F y = _)] at hRB
  obtain ⟨c, hc, p, hp, hRA⟩ := hRB
  have := hp
  let A := chartRingOver F y c
  let u : (Σ k, ι k) → A := fun q => ⟨y q / y ⟨q.1, c q.1⟩, Algebra.subset_adjoin ⟨q, rfl⟩⟩
  let φ : A →ₐ[F] IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p :=
    { (algebraMap (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p)).comp (Ideal.Quotient.mk p) with
      commutes' := fun _ => rfl }
  have hφ : ∀ a, φ a = 0 ↔ a ∈ p := by
    intro a
    have : IsFractionRing (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p) :=
      inferInstanceAs (IsFractionRing (A ⧸ p) (FractionRing (A ⧸ p)))
    show algebraMap (A ⧸ p) (IndefiniteRowSideFullHecke.Kleiman2.ResField F y c p) (Ideal.Quotient.mk p a) = 0 ↔ a ∈ p
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hmod : ∀ q, IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p q = φ (u q) := by
    intro q
    show IndefiniteRowSideFullHecke.Kleiman2.residue F y c p ((u q : A) : Ω) = _
    rw [residue_coe]
    rfl
  refine ⟨mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p),
    isMultiProjPrime_mIdealOver _ fun k => ⟨c k, ?_⟩, ?_, ?_⟩
  ·
    rw [hmod]
    have h1 : u ⟨k, c k⟩ = 1 := Subtype.ext (by simp [u, div_self (hc k)])
    rw [h1, map_one]
    exact one_ne_zero
  ·
    intro f hf
    rw [mem_mIdealOver_iff] at hf ⊢
    intro b
    have hfb := weightedHomogeneousComponent_isWeightedHomogeneous (w := NumbersDVR.blockWeight ι) b f
    have key := aeval_mul_block y (fun k => (y ⟨k, c k⟩)⁻¹) b _ hfb
    rw [hf b, zero_mul] at key
    have hu : (fun q => A.val (u q)) = fun q => y q * (fun k => (y ⟨k, c k⟩)⁻¹) q.1 := by
      funext q
      simp [u, div_eq_mul_inv]
    have h0 : aeval u (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) = 0 := by
      apply Subtype.ext
      change A.val (aeval u _) = 0
      rw [comp_aeval_apply]
      exact (congrArg (fun v => aeval v (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f)) hu).trans key
    have hw : IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p = fun q => φ (u q) := funext hmod
    rw [hw, ← comp_aeval_apply, h0, map_zero]
  ·
    rw [baseComap_mIdealOver]
    have hPx : mIdealOver F (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (fun i => ψ (Kleiman.ratio hj i))) = P := by
      ext g
      rw [mIdealOver_oneBlock_eq, Ideal.mem_comap, hpy, hmemP]
    rw [← hPx]
    ext f
    rw [mem_mIdealOver_iff, mem_mIdealOver_iff]
    refine forall_congr' fun b => ?_
    set g := weightedHomogeneousComponent (NumbersDVR.blockWeight fun _ : Unit => Fin (N + 1)) b f
    have hg : IsWeightedHomogeneous (NumbersDVR.blockWeight fun _ : Unit => Fin (N + 1)) g b :=
      weightedHomogeneousComponent_isWeightedHomogeneous b f
    let va : (Σ _ : Unit, Fin (N + 1)) → A := fun v => u ⟨k₀, e.symm v.2⟩
    let vb : (Σ _ : Unit, Fin (N + 1)) → B := fun v =>
      ⟨y ⟨k₀, e.symm v.2⟩ / y ⟨k₀, e.symm j⟩, Algebra.subset_adjoin ⟨⟨(), e.symm v.2⟩, rfl⟩⟩
    have hza : aeval (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec (IndefiniteRowSideFullHecke.Kleiman2.modVec F y c p) k₀ ∘ e.symm)) g =
        φ (aeval va g) := by
      rw [comp_aeval_apply]
      exact congrArg (fun v => aeval v g) (funext fun v => hmod _)
    have hzb : aeval (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (fun i => ψ (Kleiman.ratio hj i))) g =
        (ψ.comp (Subalgebra.inclusion hBC)) (aeval vb g) := by
      rw [comp_aeval_apply]
      refine congrArg (fun v => aeval v g) (funext fun v => ?_)
      show ψ (Kleiman.ratio hj v.2) = ψ (Subalgebra.inclusion hBC (vb v))
      congr 1
      apply Subtype.ext
      show x v.2 / x j = y ⟨k₀, e.symm v.2⟩ / y ⟨k₀, e.symm j⟩
      rw [hxv, hxv]

    set t : Ω := y ⟨k₀, c k₀⟩ / y ⟨k₀, e.symm j⟩ with ht
    have htB : t ∈ B := Algebra.subset_adjoin ⟨⟨(), c k₀⟩, rfl⟩
    have htR : t ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p := by
      rw [← hRA]
      exact mem_locIn.mpr ⟨⟨t, htB⟩, 1, one_not_mem_of_prime hq', by simp⟩
    have ht0 : t ≠ 0 := div_ne_zero (hc k₀) hyj
    have htiA : t⁻¹ ∈ A := by
      rw [ht, inv_div]
      exact Algebra.subset_adjoin ⟨⟨k₀, e.symm j⟩, rfl⟩
    have hti : t⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p :=
      mem_locIn.mpr ⟨⟨t⁻¹, htiA⟩, 1, one_not_mem_of_prime hp, by simp⟩
    have hab : ((aeval vb g : B) : Ω) = ((aeval va g : A) : Ω) * t ^ (b ()) := by
      have key := aeval_mul_block (fun v : (Σ _ : Unit, Fin (N + 1)) => ((va v : A) : Ω)) (fun _ => t) b g hg
      have hv : (fun v => B.val (vb v)) = fun v => ((va v : A) : Ω) * (fun _ : Unit => t) v.1 := by
        funext ⟨⟨⟩, i⟩
        show y ⟨k₀, e.symm i⟩ / y ⟨k₀, e.symm j⟩ = y ⟨k₀, e.symm i⟩ / y ⟨k₀, c k₀⟩ * t
        rw [ht]
        field_simp [hc k₀, hyj]
      change B.val (aeval vb g) = A.val (aeval va g) * _
      rw [comp_aeval_apply, comp_aeval_apply]
      refine (congrArg (fun v => aeval v g) hv).trans (key.trans ?_)
      simp
    rw [hza, hzb, hφ, ← RingHom.mem_ker]
    have e1 := not_mem_iff_unit_locIn (p := p) (aeval va g)
    have e2 := not_mem_iff_unit_locIn (p := q') (aeval vb g)
    rw [hab, hRA] at e2
    rw [← not_iff_not, e1]
    change _ ↔ aeval vb g ∉ q'
    rw [e2, unit_mul_pow_iff htR ht0 hti]

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
