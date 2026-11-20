import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.OneSubSmulPeirceCut

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.Grp

section Gen

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def cutM (e : R) (he : e * e = e) : Matrix n n R →* Matrix n n R :=
  GlobalTheory.PeirceDecompositionCut.peirceCut (Matrix n n R) e he

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cutM_apply (e : R) (he : e * e = e) (M : Matrix n n R) : cutM e he M = e • M + (1 - e) • 1 := rfl

/- English proof (translation)
Rewrite using `[cutM_apply, smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem cutM_sub_one (e : R) (he : e * e = e) (M : Matrix n n R) : cutM e he M - 1 = e • (M - 1) := by
  rw [cutM_apply, smul_sub, sub_smul, one_smul]; abel

/- English proof (translation)
Take `rfl : e' = 1 - e` from `by rw [← h]; ring`. Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, he]; ring`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Simplify using `only [cutM_apply, sub_sub_cancel, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', h1, h2, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]`. Rewrite using `[← add_smul]`.

Simplify using the standard rewrite rules.
-/
theorem cutM_mul (e e' : R) (he : e * e = e) (he' : e' * e' = e') (h : e + e' = 1) (M : Matrix n n R) :
    cutM e he M * cutM e' he' M = M := by
  obtain rfl : e' = 1 - e := by rw [← h]; ring
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he]; ring
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  simp only [cutM_apply, sub_sub_cancel, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, he, he', h1, h2, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  rw [← add_smul]; simp

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, he]; ring`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, h1]; ring`. Establish `hc : Formalism.UG.cT s (cutM e he M) = e • Formalism.UG.cT s M + (1 - e) • 1`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[cutM_apply, Formalism.UG.cT, hs]`. Simplify using `[cutM_apply, Formalism.UG.cT, hs, hij, Ne.symm hij]`. Rewrite using `[hc]`.

Simplify using `only [cutM_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, h]`. Rewrite using `[← add_smul]`. Simplify using the standard rewrite rules.
-/
theorem cutM_unit (s : R →+* R) (e : R) (he : e * e = e) (hs : s e = e) (J M : Matrix n n R)
    (h : Formalism.UG.cT s M * J * M = J) : Formalism.UG.cT s (cutM e he M) * J * cutM e he M = J := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, he]; ring
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, h1]; ring
  have hc : Formalism.UG.cT s (cutM e he M) = e • Formalism.UG.cT s M + (1 - e) • 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cutM_apply, Formalism.UG.cT, hs]
    · simp [cutM_apply, Formalism.UG.cT, hs, hij, Ne.symm hij]
  rw [hc]
  simp only [cutM_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
    smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, h]
  rw [← add_smul]; simp

/- English proof (translation)
Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun h i) j`. Rewrite `h2` using `[Matrix.map_apply]`. Rewrite using `[Matrix.map_apply, cutM_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, h2, map_sub, map_one, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`.

Rewrite using `[map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cutM_map {A : Type} [CommRing A] (p : R →+* A) (e : R) (he : e * e = e) (M : Matrix n n R)
    (h : M.map p = 1) : (cutM e he M).map p = 1 := by
  ext i j
  have h2 := congrFun (congrFun h i) j
  rw [Matrix.map_apply] at h2
  rw [Matrix.map_apply, cutM_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul,
    map_add, map_mul, map_mul, h2, map_sub, map_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [map_one]; ring
  · rw [map_zero]; ring

/- English proof (translation)
Rewrite using `[cutM_sub_one, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, h, map_zero, zero_mul]`.
-/
theorem cutM_kill {A : Type} [CommRing A] (p : A →+* R) (d e : A) (he : p e * p e = p e) (h : d * e = 0)
    (M : Matrix n n R) (i j : n) : p d * (cutM (p e) he M - 1) i j = 0 := by
  rw [cutM_sub_one, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, h, map_zero, zero_mul]

end Gen

variable {D : D7}

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)`.
-/
theorem incA_inj (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (cc x) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mt_mul (V : HSp D) (g g' : GA D V) : mt V (g * g') = mt V g * mt V g' := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
theorem mt_inj (V : HSp D) {g g' : GA D V} (h : mt V g = mt V g') : g = g' := Subtype.ext (Units.ext h)

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem cM_mul {k : ℕ} (a b : Matrix (Fin k) (Fin k) (AE D)) : cM (a * b) = cM a * cM b := Matrix.map_mul

/- English proof (translation)
The claim follows from `Matrix.ext fun i j => incA_inj D (congrFun (congrFun h i) j)`.
-/
theorem map_incA_inj {k : ℕ} {a b : Matrix (Fin k) (Fin k) D.host.E} (h : a.map (incA D) = b.map (incA D)) :
    a = b :=
  Matrix.ext fun i j => incA_inj D (congrFun (congrFun h i) j)

abbrev UQ (V : HSp D) : Subgroup (GL (Fin V.rank) D.host.E) :=
  Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram

/- English proof (translation)
Use `GlobalTheory.UnitarySplit.map_cond (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (cA D) (fun x => (cA_incA x).symm) V.gram ga.1` as an intermediate fact. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (cA D) (ga.1.map (incA D)) * V.gram.map (incA D) * ga.1.map (incA D) = V.gram.map (incA D) ↔ Formalism.UG.cT _ ga.1 * V.gram * ga.1 = V.gram`. Rewrite using `[← this]`. Conclude with `⟨map_incA_inj, fun h => by rw [h]⟩`.
-/
theorem bc_mem_iff (V : HSp D) (ga : GL (Fin V.rank) D.host.E) :
    Formalism.UG.bc (incA D) ga ∈ HR (AF D.host.F) D.sp.cm.sig V.gram ↔ ga ∈ UQ V := by
  have := GlobalTheory.UnitarySplit.map_cond (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (cA D)
    (fun x => (cA_incA x).symm) V.gram ga.1
  change Formalism.UG.cT (cA D) (ga.1.map (incA D)) * V.gram.map (incA D) * ga.1.map (incA D) = V.gram.map (incA D) ↔
    Formalism.UG.cT _ ga.1 * V.gram * ga.1 = V.gram
  rw [← this]
  exact ⟨map_incA_inj, fun h => by rw [h]⟩

/- English proof (translation)
Establish `h1 : γ.1 = Formalism.UG.bc (incA D) ga` using `Units.ext h`. Establish `h2 : ga ∈ UQ V` using `(bc_mem_iff V ga).1 (h1 ▸ γ.2)`. Conclude with `⟨h2, ga, h2, h1.symm⟩`.
-/
theorem rat_spec (V : HSp D) {ga : GL (Fin V.rank) D.host.E} {γ : GA D V} (h : IsRatOf V ga γ) :
    ga ∈ UQ V ∧ γ ∈ GQ V := by
  have h1 : γ.1 = Formalism.UG.bc (incA D) ga := Units.ext h
  have h2 : ga ∈ UQ V := (bc_mem_iff V ga).1 (h1 ▸ γ.2)
  exact ⟨h2, ga, h2, h1.symm⟩

/- English proof (translation)
Set `f : UQ V → GQ V` to `fun ga => ⟨⟨Formalism.UG.bc (incA D) ga.1, (bc_mem_iff V ga.1).2 ga.2⟩, ga.1, ga.2, rfl⟩`. Use `⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun ga => rfl⟩` and prove the remaining obligations. Conclude with `Subtype.ext (Units.ext (map_incA_inj (congrArg (fun x : GQ V => mt V x.1) h)))`. Introduce and unpack `⟨γ, ga, h1, h2⟩`. Conclude with `⟨⟨ga, h1⟩, Subtype.ext (Subtype.ext h2)⟩`.
-/
theorem exists_equiv (V : HSp D) : ∃ e : UQ V ≃ GQ V, ∀ ga, IsRatOf V ga.1 (e ga).1 := by
  let f : UQ V → GQ V := fun ga =>
    ⟨⟨Formalism.UG.bc (incA D) ga.1, (bc_mem_iff V ga.1).2 ga.2⟩, ga.1, ga.2, rfl⟩
  refine ⟨Equiv.ofBijective f ⟨fun a b h => ?_, ?_⟩, fun ga => rfl⟩
  · exact Subtype.ext (Units.ext (map_incA_inj (congrArg (fun x : GQ V => mt V x.1) h)))
  · rintro ⟨γ, ga, h1, h2⟩
    exact ⟨⟨ga, h1⟩, Subtype.ext (Subtype.ext h2)⟩

/- English proof (translation)
Unfold `herm Formalism.UG.hform`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x b * G a b * cc (y a) = cc (y a) * G a b * x b`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_eq {k : ℕ} (G : Matrix (Fin k) (Fin k) D.host.E) (x y : Fin k → D.host.E) :
    herm Gᵀ x y = Formalism.UG.hform (D.sp.cm.sig : D.host.E →+* D.host.E) G y x := by
  unfold herm Formalism.UG.hform
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change x b * G a b * cc (y a) = cc (y a) * G a b * x b
  ring

/- English proof (translation)
Simplify using `[Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.
-/
theorem hform_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform s J x y = (fun i => s (x i)) ⬝ᵥ J *ᵥ y := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Rewrite using `[hform_eq, hform_eq]`. Establish `: (fun i => s ((g *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s g`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]`. Rewrite using `[this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]`.
-/
theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (s : A →+* A) (J g : Matrix n n A)
    (h : Formalism.UG.cT s g * J * g = J) (x y : n → A) :
    Formalism.UG.hform s J (g *ᵥ x) (g *ᵥ y) = Formalism.UG.hform s J x y := by
  rw [hform_eq, hform_eq]
  have : (fun i => s ((g *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s g := by
    funext i
    simp [Formalism.UG.cT, Matrix.mulVec, Matrix.vecMul, dotProduct, mul_comm]
  rw [this, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

/- English proof (translation)
Unfold `IsUn`. Rewrite using `[C.m.gT]`. Simplify using `only [herm_eq]`. Conclude with `⟨fun h => GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun x y => h y x, fun h x y => hform_mulVec _ _ _ h _ _⟩`.
-/
theorem isUn_iff {S T : HSp D} (C : Ctx S T) (ga : GL (Fin T.rank) D.host.E) : IsUn C.X ga ↔ ga ∈ UQ T := by
  unfold IsUn
  rw [C.m.gT]
  simp only [herm_eq]
  exact ⟨fun h => GlobalTheory.UnitarySplit.mem_of_form _ _ _ fun x y => h y x, fun h x y => hform_mulVec _ _ _ h _ _⟩

/- English proof (translation)
The claim follows from `star_star x`.
-/
theorem cc_cc' (x : D.host.E) : cc (cc x) = x := star_star x

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

/- English proof (translation)
The claim follows from `Matrix.ext fun _ _ => cc_cc' _`.
-/
theorem map_sg_sg {k : ℕ} (a : Matrix (Fin k) (Fin k) D.host.E) : (a.map (sg D)).map (sg D) = a :=
  Matrix.ext fun _ _ => cc_cc' _

/- English proof (translation)
Use `congrArg (fun m => m.map (sg D)) h` as an intermediate fact. Simplify using `only [Matrix.map_mul] at this`. Rewrite `this` using `[Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `this`.
-/
theorem conj_unit {k : ℕ} (a : Matrix (Fin k) (Fin k) D.host.E) (h : Formalism.UG.cT (sg D) a * a = 1) :
    Formalism.UG.cT (sg D) (a.map (sg D)) * a.map (sg D) = 1 := by
  have := congrArg (fun m => m.map (sg D)) h
  simp only [Matrix.map_mul] at this
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

/- English proof (translation)
Take `⟨e, he⟩` from `exists_equiv S`. Establish `hm : ∀ g : GL (Fin S.rank) D.host.E, g ∈ UQ S ↔ Formalism.UG.cT (sg D) g.1 * g.1 = 1` using `fun g => by`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (sg D) g.1 * S.gram * g.1 = S.gram ↔ _`. Rewrite using `[hS, Matrix.mul_one]`. Set `e0 : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ UQ S` to `{ toFun := fun h => ⟨⟨h.1.map (sg D), Formalism.UG.cT (sg D) (h.1.map (sg D)), mul_eq_one_comm.1 (conj_unit h.1 h.2), conj_unit h.1 h.2⟩, (hm _).2 (conj_unit h.1 h.2)⟩ invFun := fun g => ⟨g.1.1.map (sg D), conj_unit _ ((hm _).1 g.2)⟩ left_inv := fun h => Subtype.ext (map_sg_sg _) …`.

Use `⟨e0.trans e, fun h => ?_⟩` and prove the remaining obligations. Establish `: mt S (e (e0 h)).1 = (h.1.map (sg D)).map (incA D)` using `he (e0 h)`. Express the relevant statement in the definitionally equal form `cM (mt S (e (e0 h)).1) = _`. Rewrite using `[this]`. Use extensionality with `i j`.

Conclude with `(cA_incA _).trans (congrArg (incA D) (cc_cc' _))`.
-/
theorem exists_equiv_std (S : HSp D) (hS : S.gram = 1) :
    ∃ e : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ GQ S,
      ∀ h, cM (mt S (e h).1) = h.1.map (incA D) := by
  obtain ⟨e, he⟩ := exists_equiv S
  have hm : ∀ g : GL (Fin S.rank) D.host.E, g ∈ UQ S ↔ Formalism.UG.cT (sg D) g.1 * g.1 = 1 := fun g => by
    change Formalism.UG.cT (sg D) g.1 * S.gram * g.1 = S.gram ↔ _
    rw [hS, Matrix.mul_one]
  let e0 : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ UQ S :=
    { toFun := fun h => ⟨⟨h.1.map (sg D), Formalism.UG.cT (sg D) (h.1.map (sg D)),
          mul_eq_one_comm.1 (conj_unit h.1 h.2), conj_unit h.1 h.2⟩, (hm _).2 (conj_unit h.1 h.2)⟩
      invFun := fun g => ⟨g.1.1.map (sg D), conj_unit _ ((hm _).1 g.2)⟩
      left_inv := fun h => Subtype.ext (map_sg_sg _)
      right_inv := fun g => Subtype.ext (Units.ext (map_sg_sg _)) }
  refine ⟨e0.trans e, fun h => ?_⟩
  have : mt S (e (e0 h)).1 = (h.1.map (sg D)).map (incA D) := he (e0 h)
  change cM (mt S (e (e0 h)).1) = _
  rw [this]
  ext i j
  exact (cA_incA _).trans (congrArg (incA D) (cc_cc' _))

/- English proof (translation)
Take `⟨e, -⟩` from `exists_equiv V`. Establish `: Countable D.host.E` using `Finsupp.Countable.of_moduleFinite (R := ℚ)`. Establish `: Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E)` using `inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))`. Establish `: Countable (GL (Fin V.rank) D.host.E)` using `Units.val_injective.countable`. Conclude with `e.symm.injective.countable`.
-/
theorem countable_GQ (V : HSp D) : Countable (GQ V) := by
  obtain ⟨e, -⟩ := exists_equiv V
  have : Countable D.host.E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  have : Countable (Matrix (Fin V.rank) (Fin V.rank) D.host.E) :=
    inferInstanceAs (Countable (Fin V.rank → Fin V.rank → D.host.E))
  have : Countable (GL (Fin V.rank) D.host.E) := Units.val_injective.countable
  exact e.symm.injective.countable

/- English proof (translation)
Use extensionality with `i j`. Conclude with `GlobalTheory.UnitarySplit.map_sig _ _ _`.
-/
theorem fmtC_eq (V : HSp D) (g : GA D V) : fmtC V g = (fmt V g).map (sigR (Af D.host.F) D.sp.cm.sig) := by
  ext i j
  exact GlobalTheory.UnitarySplit.map_sig _ _ _

/- English proof (translation)
Establish `he : algebraMap _ (AE D) ε * algebraMap _ (AE D) ε = algebraMap _ (AE D) ε`. Rewrite using `[← RingHom.map_mul, hε]`. Establish `hs : cA D (algebraMap _ (AE D) ε) = algebraMap _ (AE D) ε`. Express the relevant statement in the definitionally equal form `ε ⊗ₜ[D.host.F] D.sp.cm.sig 1 = ε ⊗ₜ[D.host.F] 1`. Rewrite using `[map_one]`.

Establish `h0 : infHom V f = 1` using `hf`. Establish `h1 : (mt V f).map (infPart D) = 1` using `congrArg Units.val h0`. Establish `hu : Formalism.UG.cT (cA D) (mt V f) * JR (AF D.host.F) V.gram * mt V f = JR (AF D.host.F) V.gram` using `f.2`. Establish `hu'` using `cutM_unit (cA D) _ he hs _ _ hu`. Take `⟨u, hu1⟩ : ∃ u : GL (Fin V.rank) (AE D), u.1 = cutM _ he (mt V f)` from `⟨Units.map (cutM _ he) (matHom V f), rfl⟩`.

Establish `h2` using `cutM_map (infPart D) _ he _ h1`. Rewrite `hu'`, `h2` using `[← hu1]`. Establish `h3 : infHom V ⟨u, hu'⟩ = 1` using `Units.ext h2`. Conclude with `⟨he, ⟨u, hu'⟩, h3, hu1⟩`.
-/
theorem exists_cut (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (f : GA D V) (hf : f ∈ GfC V) :
    ∃ (he : algebraMap _ (AE D) ε * algebraMap _ (AE D) ε = algebraMap _ (AE D) ε) (g : GA D V),
      g ∈ GfC V ∧ mt V g = cutM _ he (mt V f) := by
  have he : algebraMap _ (AE D) ε * algebraMap _ (AE D) ε = algebraMap _ (AE D) ε := by
    rw [← RingHom.map_mul, hε]
  have hs : cA D (algebraMap _ (AE D) ε) = algebraMap _ (AE D) ε := by
    change ε ⊗ₜ[D.host.F] D.sp.cm.sig 1 = ε ⊗ₜ[D.host.F] 1
    rw [map_one]
  have h0 : infHom V f = 1 := hf
  have h1 : (mt V f).map (infPart D) = 1 := congrArg Units.val h0
  have hu : Formalism.UG.cT (cA D) (mt V f) * JR (AF D.host.F) V.gram * mt V f = JR (AF D.host.F) V.gram := f.2
  have hu' := cutM_unit (cA D) _ he hs _ _ hu
  obtain ⟨u, hu1⟩ : ∃ u : GL (Fin V.rank) (AE D), u.1 = cutM _ he (mt V f) :=
    ⟨Units.map (cutM _ he) (matHom V f), rfl⟩
  have h2 := cutM_map (infPart D) _ he _ h1
  rw [← hu1] at hu' h2
  have h3 : infHom V ⟨u, hu'⟩ = 1 := Units.ext h2
  exact ⟨he, ⟨u, hu'⟩, h3, hu1⟩

/- English proof (translation)
The claim follows from `Subtype.ext (funext h)`.
-/
theorem af_ext {F : Type} [Field F] [NumberField F] {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) : a = b :=
  Subtype.ext (funext h)

/- English proof (translation)
Use `⟨⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩, fun v hv => if_pos hv, fun v hv => if_neg hv⟩` and prove the remaining obligations. Use `beta_reduce`. Use `split_ifs`. Conclude with `one_mem (v.adicCompletionIntegers F)`. Conclude with `zero_mem (v.adicCompletionIntegers F)`.
-/
theorem exists_indicator {F : Type} [Field F] [NumberField F] (P : HeightOneSpectrum (𝓞 F) → Prop) :
    ∃ e : Af F, (∀ v, P v → evalV F v e = 1) ∧ ∀ v, ¬ P v → evalV F v e = 0 := by
  refine ⟨⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩,
    fun v hv => if_pos hv, fun v hv => if_neg hv⟩
  beta_reduce
  split_ifs
  · exact one_mem (v.adicCompletionIntegers F)
  · exact zero_mem (v.adicCompletionIntegers F)

/- English proof (translation)
The claim follows from `Prod.ext (mul_zero _) rfl`.
-/
theorem pair_mul {F : Type} [Field F] [NumberField F] (a b : Af F) : pairA F 0 a * pairA F 0 b = pairA F 0 (a * b) :=
  Prod.ext (mul_zero _) rfl

/- English proof (translation)
Take `⟨α, h1, h0⟩` from `exists_indicator (F := D.host.F) fun v => I ≤ v.asIdeal`. Establish `hα : α * α = α` using `af_ext fun v => by`. Rewrite using `[map_mul]`. Distinguish the cases in `hv : I ≤ v.asIdeal`. Rewrite using `[h1 v hv, mul_one]`.

Rewrite using `[h0 v hv, mul_zero]`. Use `set ε := pairA D.host.F 0 α with hεd`. Establish `hε : ε * ε = ε` using `by rw [hεd, pair_mul, hα]`. Establish `hε' : (1 - ε) * (1 - ε) = 1 - ε` using `by linear_combination hε`. Take `⟨he₁, f₁, hf₁, m₁⟩` from `exists_cut V _ hε' f hf`.

Take `⟨he₂, f₂, hf₂, m₂⟩` from `exists_cut V _ hε f hf`. Establish `e1 : f = f₁ * f₂` using `mt_inj V (by`. Rewrite using `[mt_mul, m₁, m₂, cutM_mul _ _ _ _ (by rw [← RingHom.map_add, sub_add_cancel, RingHom.map_one])])`. Establish `e2 : f = f₂ * f₁` using `mt_inj V (by`. Rewrite using `[mt_mul, m₁, m₂, cutM_mul _ _ _ _ (by rw [← RingHom.map_add, add_sub_cancel, RingHom.map_one])])`.

Use `⟨f₁, hf₁, f₂, hf₂, e1, e1.symm.trans e2, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `v hv δ ⟨β, rfl, b1, b0⟩ i j`. Establish `: β * α = β` using `af_ext fun w => by`. Rewrite using `[map_mul]`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[h1 w hv, mul_one]`. Rewrite using `[b0 w hw, zero_mul]`. Rewrite using `[m₁]`. Conclude with `cutM_kill _ _ _ he₁ (by rw [mul_sub, hεd, pair_mul, this, mul_one, sub_self]) _ i j`.

Introduce and unpack `v hv δ ⟨β, rfl, b1, b0⟩ i j`. Establish `: β * α = 0` using `af_ext fun w => by`. Rewrite using `[map_mul, map_zero]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[h0 w hv, mul_zero]`. Rewrite using `[b0 w hw, zero_mul]`. Rewrite using `[m₂]`. Conclude with `cutM_kill _ _ _ he₂ (by rw [hεd, pair_mul, this]; rfl) _ i j`.
-/
theorem exists_at_off (V : HSp D) (I : Ideal (𝓞 D.host.F)) (f : GA D V) (hf : f ∈ GfC V) :
    ∃ f₁ ∈ GfC V, ∃ f₂ ∈ GfC V, f = f₁ * f₂ ∧ f₁ * f₂ = f₂ * f₁ ∧ TrivAt V I f₁ ∧ TrivOff V I f₂ := by
  obtain ⟨α, h1, h0⟩ := exists_indicator (F := D.host.F) fun v => I ≤ v.asIdeal
  have hα : α * α = α := af_ext fun v => by
    rw [map_mul]
    by_cases hv : I ≤ v.asIdeal
    · rw [h1 v hv, mul_one]
    · rw [h0 v hv, mul_zero]
  set ε := pairA D.host.F 0 α with hεd
  have hε : ε * ε = ε := by rw [hεd, pair_mul, hα]
  have hε' : (1 - ε) * (1 - ε) = 1 - ε := by linear_combination hε
  obtain ⟨he₁, f₁, hf₁, m₁⟩ := exists_cut V _ hε' f hf
  obtain ⟨he₂, f₂, hf₂, m₂⟩ := exists_cut V _ hε f hf
  have e1 : f = f₁ * f₂ := mt_inj V (by
    rw [mt_mul, m₁, m₂, cutM_mul _ _ _ _ (by rw [← RingHom.map_add, sub_add_cancel, RingHom.map_one])])
  have e2 : f = f₂ * f₁ := mt_inj V (by
    rw [mt_mul, m₁, m₂, cutM_mul _ _ _ _ (by rw [← RingHom.map_add, add_sub_cancel, RingHom.map_one])])
  refine ⟨f₁, hf₁, f₂, hf₂, e1, e1.symm.trans e2, ?_, ?_⟩
  · rintro v hv δ ⟨β, rfl, b1, b0⟩ i j
    have : β * α = β := af_ext fun w => by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1 w hv, mul_one]
      · rw [b0 w hw, zero_mul]
    rw [m₁]
    exact cutM_kill _ _ _ he₁ (by rw [mul_sub, hεd, pair_mul, this, mul_one, sub_self]) _ i j
  · rintro v hv δ ⟨β, rfl, b1, b0⟩ i j
    have : β * α = 0 := af_ext fun w => by
      rw [map_mul, map_zero]
      by_cases hw : w = v
      · subst hw; rw [h0 w hv, mul_zero]
      · rw [b0 w hw, zero_mul]
    rw [m₂]
    exact cutM_kill _ _ _ he₂ (by rw [hεd, pair_mul, this]; rfl) _ i j

/- English proof (translation)
Introduce `D S T C`. Use `⟨?_, fun γ γ' ga ga' h h' => ⟨?_, ?_, (rat_spec T h).2, (isUn_iff C ga).2 (rat_spec T h).1, ?_⟩, exists_equiv_std S C.m.gS, fun V => ⟨countable_GQ V, fun g g' => ⟨rfl, ?_, ?_, mt_inj V⟩, (GlobalTheory.UnitarySplit.real_finite_split D V).1, fun a ha => ?_, fun I _ f hf => exists_a …` and prove the remaining obligations. Take `⟨e, he⟩` from `exists_equiv T`. Conclude with `⟨(Equiv.subtypeEquivRight (isUn_iff C)).trans e, fun ga => he ⟨ga.1, (isUn_iff C _).1 ga.2⟩⟩`. Unfold `IsRatOf at *`.

Rewrite using `[mt_mul, h, h', Units.val_mul, Matrix.map_mul]`. Establish `h1 : matHom T γ = Formalism.UG.bc (incA D) ga` using `Units.ext h`. Establish `h2 : matHom T γ⁻¹ = Formalism.UG.bc (incA D) ga⁻¹` using `by rw [map_inv, map_inv, h1]`. Conclude with `congrArg Units.val h2`. Unfold `IsRatOf at *`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `Units.ext (map_incA_inj (h.symm.trans h'))`. Introduce and unpack `rfl`. Conclude with `mt_inj T (h.trans h'.symm)`.

Unfold `fmt`. Rewrite using `[mt_mul, Matrix.map_mul]`. Unfold `fmtC`. Rewrite using `[mt_mul, cM_mul, Matrix.map_mul]`. Establish `h1 : fmt V a = 1` using `congrArg Units.val ha`.

Use `⟨h1, ?_, (GlobalTheory.UnitarySplit.real_finite_split D V).2.1 a ha⟩` and prove the remaining obligations. Rewrite using `[fmtC_eq, h1, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem rational_points_and_parts : ∀ (D : D7) (S T : HSp D) (C : Ctx S T), (∃ e : {ga : GL (Fin T.rank) D.host.E // IsUn C.X ga} ≃ GQ T, ∀ ga, IsRatOf T ga.1 (e ga).1) ∧ (∀ (γ γ' : GA D T) ga ga', IsRatOf T ga γ → IsRatOf T ga' γ' → IsRatOf T (ga * ga') (γ * γ') ∧ IsRatOf T ga⁻¹ γ⁻¹ ∧ γ ∈ GQ T ∧ IsUn C.X ga ∧ (γ = γ' ↔ ga = ga')) ∧ (∃ e : {h : Matrix (Fin S.rank) (Fin S.rank) D.host.E // ccT h * h = 1} ≃ GQ S, ∀ h, cM (mt S (e h).1) = h.1.map (incA D)) ∧ ∀ V : HSp D, Countable (GQ V) ∧ (∀ g g' : GA D V, mt V (g * g') = mt V g * mt V g' ∧ fmt V (g * g') = fmt V g * fmt V g' ∧ fmtC V (g * g') = fmtC V g * fmtC V g' ∧ (mt V g = mt V g' → g = g')) ∧ (∀ g : GA D V, ∃ a ∈ GinfC V, ∃ f ∈ GfC V, g = a * f) ∧ (∀ a ∈ GinfC V, fmt V a = 1 ∧ fmtC V a = 1 ∧ ∀ f ∈ GfC V, a * f = f * a) ∧ ∀ (I : Ideal (𝓞 D.host.F)), I ≠ ⊥ → ∀ f ∈ GfC V, ∃ f₁ ∈ GfC V, ∃ f₂ ∈ GfC V, f = f₁ * f₂ ∧ f₁ * f₂ = f₂ * f₁ ∧ TrivAt V I f₁ ∧ TrivOff V I f₂ := by
  intro D S T C
  refine ⟨?_, fun γ γ' ga ga' h h' => ⟨?_, ?_, (rat_spec T h).2, (isUn_iff C ga).2 (rat_spec T h).1, ?_⟩,
    exists_equiv_std S C.m.gS, fun V => ⟨countable_GQ V, fun g g' => ⟨rfl, ?_, ?_, mt_inj V⟩,
      (GlobalTheory.UnitarySplit.real_finite_split D V).1, fun a ha => ?_, fun I _ f hf => exists_at_off V I f hf⟩⟩
  · obtain ⟨e, he⟩ := exists_equiv T
    exact ⟨(Equiv.subtypeEquivRight (isUn_iff C)).trans e, fun ga => he ⟨ga.1, (isUn_iff C _).1 ga.2⟩⟩
  · unfold IsRatOf at *
    rw [mt_mul, h, h', Units.val_mul, Matrix.map_mul]
  · have h1 : matHom T γ = Formalism.UG.bc (incA D) ga := Units.ext h
    have h2 : matHom T γ⁻¹ = Formalism.UG.bc (incA D) ga⁻¹ := by rw [map_inv, map_inv, h1]
    exact congrArg Units.val h2
  · unfold IsRatOf at *
    constructor
    · rintro rfl
      exact Units.ext (map_incA_inj (h.symm.trans h'))
    · rintro rfl
      exact mt_inj T (h.trans h'.symm)
  · unfold fmt
    rw [mt_mul, Matrix.map_mul]
  · unfold fmtC
    rw [mt_mul, cM_mul, Matrix.map_mul]
  · have h1 : fmt V a = 1 := congrArg Units.val ha
    refine ⟨h1, ?_, (GlobalTheory.UnitarySplit.real_finite_split D V).2.1 a ha⟩
    rw [fmtC_eq, h1, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.Ker.Grp

end
