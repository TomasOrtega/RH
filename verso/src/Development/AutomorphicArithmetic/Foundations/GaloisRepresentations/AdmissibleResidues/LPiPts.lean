import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealAway
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoSub
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoPick
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsoRefine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

attribute [local instance 2000] UpperTheory.V.W.coefLocal

/- English proof (translation)
Take `⟨t, ht⟩` from `t`. Express the relevant statement in the definitionally equal form `∀ y y' : Y, (y' : M) = φ y → (t y' : M) = φ (t y)`. Proceed by induction on `ht using Algebra.adjoin_induction with`. Consider the case `mem t ht`. Take `⟨i, hi⟩` from `ht`.

Introduce `y y' e`. Rewrite using `[hi, hi, e]`. Conclude with `(LinearMap.congr_fun (h i).eq y).symm`. Consider the case `algebraMap a`. Introduce `y y' e`.

Simplify using `[Module.algebraMap_end_apply, e]`. Consider the case `add s t _ _ hs ht`. Introduce `y y' e`. Simplify using `only [LinearMap.add_apply, Submodule.coe_add, map_add, hs y y' e, ht y y' e]`. Consider the case `mul s t _ _ hs ht => exact fun y y' e => hs _ _ (ht y y' e)`.
-/
private theorem piPts_hecke {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M)
    (op : ι → Module.End A M) (φ : Module.End A M) (h : ∀ i, Commute φ (op i)) (t : heckeAlg Y op) :
    ∀ y y' : Y, (y' : M) = φ y → ((t : Module.End A Y) y' : M) = φ ((t : Module.End A Y) y) := by
  obtain ⟨t, ht⟩ := t
  change ∀ y y' : Y, (y' : M) = φ y → (t y' : M) = φ (t y)
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨i, hi⟩ := ht
    intro y y' e
    rw [hi, hi, e]
    exact (LinearMap.congr_fun (h i).eq y).symm
  | algebraMap a =>
    intro y y' e
    simp [Module.algebraMap_end_apply, e]
  | add s t _ _ hs ht =>
    intro y y' e
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, hs y y' e, ht y y' e]
  | mul s t _ _ hs ht => exact fun y y' e => hs _ _ (ht y y' e)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(W.GDet.repAlg ρ (Polynomial A) _).det = _`. Rewrite using `[map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]`. Use `congr 1`. Use extensionality with `i j : 2`. Apply the tactic sequence `by_cases h : i = j <;> simp [W.GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]`.
-/
private theorem piPts_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (W.GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

/- English proof (translation)
Set `S : N →+ V` to `AddMonoidHom.mk' s ha`. Distinguish the cases in `h : i ∈ (b.repr z).support`. Use `linearIndependent_iff'.1 hi (b.repr z).support (fun i => φ (b.repr z i)) ?_ i h` and prove the remaining obligations. Establish `: S z = S (Finsupp.linearCombination A b (b.repr z))` using `by rw [b.linearCombination_repr]`. Rewrite `this` using `[Finsupp.linearCombination_apply, Finsupp.sum, map_sum]`.

Rewrite using `[← hz]`. Conclude with `(Finset.sum_congr rfl fun i _ => (hs _ _).symm).trans this.symm`. Rewrite using `[Finsupp.notMem_support_iff.1 h, map_zero]`.
-/
private theorem piPts_coord {A N V κ : Type} [CommRing A] [AddCommGroup N] [Module A N] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ A N) (φ : A →+* ℂ) (s : N → V) (ha : ∀ x y, s (x + y) = s x + s y)
    (hs : ∀ a x, s (a • x) = φ a • s x) (hi : LinearIndependent ℂ fun i => s (b i)) (z : N) (hz : s z = 0) (i : κ) :
    φ (b.repr z i) = 0 := by
  let S : N →+ V := AddMonoidHom.mk' s ha
  by_cases h : i ∈ (b.repr z).support
  · refine linearIndependent_iff'.1 hi (b.repr z).support (fun i => φ (b.repr z i)) ?_ i h
    have : S z = S (Finsupp.linearCombination A b (b.repr z)) := by rw [b.linearCombination_repr]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at this
    rw [← hz]
    exact (Finset.sum_congr rfl fun i _ => (hs _ _).symm).trans this.symm
  · rw [Finsupp.notMem_support_iff.1 h, map_zero]

/- English proof (translation)
Use `LinearMap.ext fun f => funext fun x => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `X.ra τ u (X.rp A m b f) x = X.ra τ u f (x * (1, b))`. Rewrite using `[Frame.ra_apply, Frame.ra_apply]`. Express the relevant statement in the definitionally equal form `Matrix.mulVec _ (f _) = _`. Simplify using `[mul_assoc]`.
-/
private theorem piPts_rp {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.rp A m b) := by
  refine LinearMap.ext fun f => funext fun x => ?_
  change X.ra τ u (X.rp A m b f) x = X.ra τ u f (x * (1, b))
  rw [Frame.ra_apply, Frame.ra_apply]
  change Matrix.mulVec _ (f _) = _
  simp [mul_assoc]

/- English proof (translation)
The claim follows from `W.GDet.ext fun _ _ _ _ => rfl`.
-/
private theorem piPts_mm {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : W.GDet n A G)
    (f : A →+* B) (f' : B →+* C) : (D.map f).map f' = D.map (f'.comp f) :=
  W.GDet.ext fun _ _ _ _ => rfl

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)

/- English proof (translation)
Break down `i with ⟨w, j⟩ | ⟨v, j⟩` into its components or cases. Use `finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun i => ?_` and prove the remaining obligations. Conclude with `(hH.sectionsCommuteAtSplit q w.1 w.2 g _).map (H.X.ra (H.τA A))`. Use `finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun i => ?_` and prove the remaining obligations. Conclude with `piPts_rp H.X (H.τA A) _ _`.
-/
private theorem piPts_comm (hH : H.Ax) (A : Type) [CommRing A] [Algebra c.O A] (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with ⟨w, j⟩ | ⟨v, j⟩
  · refine finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _)
      (fun _ _ => Commute.add_right) fun i => ?_
    exact (hH.sectionsCommuteAtSplit q w.1 w.2 g _).map (H.X.ra (H.τA A))
  · refine finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _)
      (fun _ _ => Commute.add_right) fun i => ?_
    exact piPts_rp H.X (H.τA A) _ _

/- English proof (translation)
Take `⟨P, hP⟩` from `AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat Y'.r) Y.ss Y'.ss fun g => by`. Rewrite using `[← piPts_chi, ← piPts_chi, h]`. Conclude with `UpperTheory.GalN.V.woConj (Y'.atQ q B hB rc hrc) (hH.Q_away q) (r' := Y.r.comp H.prj) P fun g => Units.ext (hP _)`.
-/
private theorem piPts_conj (hH : H.Ax) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d : ℕ}
    (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y Y' : H.Part ι lam ξ)
    (h : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat Y'.r)) (q : H.Q) (B : ValuationSubring Ω) (hB : IsPlaceOver B (H.wq q))
    (rc : IrrGL ((H.wq q).adicCompletion L) → WD hB) (hrc : IsRec hB rc) :
    UpperTheory.V.Lev.WO ι (Y.r.comp H.prj) (rc (algNorm (Y'.σq q))) := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat Y'.r) Y.ss Y'.ss fun g => by
    rw [← piPts_chi, ← piPts_chi, h]
  exact UpperTheory.GalN.V.woConj (Y'.atQ q B hB rc hrc) (hH.Q_away q) (r' := Y.r.comp H.prj) P fun g => Units.ext (hP _)

/- English proof (translation)
Take `⟨ρ, -, h1, h2, -⟩` from `piBasic L Ω l n c H hH A θ hθ a`. Establish `mono : ∀ K K' : H.Lev, (∀ q, K'.1 q ≤ K.1 q) → H.MK θ a K ≤ H.MK θ a K'` using `fun K K' h => by`. Rewrite using `[← h1, ← h1]`. Conclude with `Submodule.map_mono fun v hv u hu => hv u fun q hq => h q (hu q hq)`. Proceed by induction on `s using Finset.induction with`.

Consider the case `empty => exact ⟨(h2 0).choose, by simp⟩`. Consider the case `insert f s _ ih`. Take `⟨K, hK⟩` from `ih`. Take `⟨K', hK'⟩` from `h2 f`. Set `K'' : H.Lev` to `⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1, (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩`.

Use `⟨K'', fun x hx => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `mono K' K'' (fun q => inf_le_right) hK'`. Conclude with `mono K K'' (fun q => inf_le_left) (hK x hx)`.
-/
private theorem piPts_dir (hH : H.Ax) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
    (hθ : H.IsWt θ) (a : H.Op → c.O) (s : Finset (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) :
    ∃ K, ∀ f ∈ s, (f : H.X.Fn A H.m) ∈ H.MK θ a K := by
  classical
  obtain ⟨ρ, -, h1, h2, -⟩ := piBasic L Ω l n c H hH A θ hθ a
  have mono : ∀ K K' : H.Lev, (∀ q, K'.1 q ≤ K.1 q) → H.MK θ a K ≤ H.MK θ a K' := fun K K' h => by
    rw [← h1, ← h1]
    exact Submodule.map_mono fun v hv u hu => hv u fun q hq => h q (hu q hq)
  induction s using Finset.induction with
  | empty => exact ⟨(h2 0).choose, by simp⟩
  | insert f s _ ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨K', hK'⟩ := h2 f
    let K'' : H.Lev := ⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩
    refine ⟨K'', fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact mono K' K'' (fun q => inf_le_right) hK'
    · exact mono K K'' (fun q => inf_le_left) (hK x hx)

end

/- English proof (translation)
Establish `hT : ∀ t, ∃ T : V →ₗ[ℂ] V, ∀ f, T (s f) = s (α t f)` using `fun t => by`. Use `PiLin.exists_desc _ _ fun u hu => ?_` and prove the remaining obligations. Take `⟨K, hK⟩` from `dir (insert z u.support)`. Take `⟨act, a1, -⟩` from `lev K (hK z (Finset.mem_insert_self _ _))`. Establish `hm : ∀ f : u.support, mem K f` using `fun f => hK _ (Finset.mem_insert_of_mem f.2)`.

Rewrite `hu`, the goal using `[Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort]`. Establish `h0 : ∑ f : u.support, u f • (⟨s f, hEK K f (hm f)⟩ : EK K) = 0` using `Subtype.ext (by`. Rewrite using `[Submodule.coe_sum]`. Conclude with `hu)`. Establish `h3` using `congrArg (fun F => (act t F : V)) h0`.

Simplify using `only [map_sum, map_smul, map_zero, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h3`. Rewrite using `[← h3]`. Conclude with `Finset.sum_congr rfl fun f _ => by rw [a1 t f (hm f)]`. Use `choose T hT using hT`. Set `E` to `Submodule.span ℂ (Set.range s)`.

Establish `hE : ∀ f, s f ∈ E` using `fun f => Submodule.subset_span ⟨f, rfl⟩`. Set `J` to `{j : I × X × Submodule ℂ V // j.2.2 ≤ Yp j.1 ⊓ E ∧ rel j.1 j.2.1 ∧ ∀ t, ∀ F ∈ j.2.2, T t F = χ j.2.1 t • F}`. Establish `hsup : E = ⨆ j : J, j.1.2.2`. Use `le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun j => j.2.1.trans inf_le_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, rfl⟩`.

Take `⟨K, hK⟩` from `dir {z, f}`. Take `⟨act, a1, a3, a4⟩` from `lev K (hK z (by simp))`. Establish `hle : EK K ≤ E` using `(hEK' K).trans (Submodule.span_mono (Set.image_subset_range _ _))`. Establish `hsp : Submodule.span ℂ (s '' {f | mem K f}) ≤ EK K` using `Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `hEK K y hy)`. Establish `hact : ∀ t F (hF : F ∈ Submodule.span ℂ (s '' {f | mem K f})), T t F = act t ⟨F, hsp hF⟩` using `fun t F hF => by`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem F hF`. Take `⟨y, hy, rfl⟩` from `hF`.

Conclude with `(hT t y).trans (a1 t y hy).symm`. Consider the case `zero => exact (map_zero _).trans (congrArg Subtype.val (map_zero (act t))).symm`. Consider the case `add F F' hF hF' h h'`. Rewrite using `[map_add, h, h']`. Conclude with `(congrArg Subtype.val (map_add (act t) ⟨F, hsp hF⟩ ⟨F', hsp hF'⟩)).symm`.

Consider the case `smul u F hF h`. Rewrite using `[map_smul, h]`. Conclude with `(congrArg Subtype.val (map_smul (act t) u ⟨F, hsp hF⟩)).symm`. Use `(show EK K ≤ ⨆ j : J, j.1.2.2 from ?_) (hEK K f (hK f (by simp)))` and prove the remaining obligations. Use `a3.trans (iSup_le fun i => ?_)` and prove the remaining obligations.

Distinguish the cases in `hY : Yp i ⊓ EK K = ⊥`. Rewrite using `[hY]`. Conclude with `bot_le`. Take `⟨x, b1, b2⟩` from `a4 i hY`. Conclude with `le_iSup (fun j : J => j.1.2.2) ⟨(i, x, Yp i ⊓ EK K), inf_le_inf_left _ hle, b1, fun t F hF => by`.

Rewrite using `[hact t F (hEK' K hF.2), b2 t ⟨F, hF.2⟩ hF.1]`. Use the proof step `rfl⟩`. Take `⟨j0, Y, p, -, y1, y2, y3, y4, y5⟩` from `PiLin.exists_proj (J := J) T π E (fun g => show E ≤ E.comap (π g) from Submodule.span_le.2 (by`. Introduce and unpack `_ ⟨f, rfl⟩`. Express the relevant statement in the definitionally equal form `π g (s f) ∈ E`.

Rewrite using `[← h1]`. Conclude with `hE _))`. Use the proof step `(fun t g F hF => LinearMap.eqOn_span' (f := T t ∘ₗ π g) (g := π g ∘ₗ T t) (by`. Introduce and unpack `_ ⟨f, rfl⟩`. Simplify using `only [LinearMap.comp_apply]`.

Rewrite using `[← h1, hT, hT, h2, h1]) hF)`. Use the proof step `(fun j => j.1.2.2) (fun j => χ j.1.2.1) (fun j => j.2.2.2) hsup (s z) (hE z) hz`. Use `⟨j0.1.1, j0.1.2.1, Y, p, j0.2.2.1, y1, y2, fun t f => ?_, fun g f => ?_, fun Z hZ => y5.trans (iSup_le fun j => ?_)⟩` and prove the remaining obligations. Rewrite using `[← hT, y3 t _ (hE f)]`. Rewrite using `[h1, y4 g _ (hE f)]`.

Conclude with `(j.1.2.1.trans inf_le_left).trans (hZ _ _ j.1.2.2.1 j.2)`.
-/
private theorem piPts_abs {M V R G Lev X : Type} {I : Type 1} [AddCommGroup V] [Module ℂ V]
    (s : M → V) (z : M) (hz : s z ≠ 0) (α : R → M → M) (ρ : G → M → M) (π : G → V →ₗ[ℂ] V) (mem : Lev → M → Prop)
    (dir : ∀ u : Finset M, ∃ K, ∀ f ∈ u, mem K f) (EK : Lev → Submodule ℂ V) (hEK : ∀ K f, mem K f → s f ∈ EK K)
    (hEK' : ∀ K, EK K ≤ Submodule.span ℂ (s '' {f | mem K f})) (Yp : I → Submodule ℂ V) (χ : X → R → ℂ) (rel : I → X → Prop)
    (h1 : ∀ g f, s (ρ g f) = π g (s f)) (h2 : ∀ g t f, α t (ρ g f) = ρ g (α t f))
    (lev : ∀ K, mem K z → ∃ act : R → Module.End ℂ (EK K), (∀ t f hf, (act t ⟨s f, hEK K f hf⟩ : V) = s (α t f)) ∧
      (EK K ≤ ⨆ i, Yp i ⊓ EK K) ∧
      ∀ i, Yp i ⊓ EK K ≠ ⊥ → ∃ x, rel i x ∧ ∀ t (F : EK K), (F : V) ∈ Yp i → act t F = χ x t • F) :
    ∃ (i0 : I) (x0 : X) (Y : Submodule ℂ V) (p : V →ₗ[ℂ] Y), rel i0 x0 ∧ (∀ g, ∀ F ∈ Y, π g F ∈ Y) ∧ p (s z) ≠ 0 ∧
      (∀ t f, p (s (α t f)) = χ x0 t • p (s f)) ∧ (∀ g f, (p (s (ρ g f)) : V) = π g (p (s f))) ∧
      ∀ Z : Submodule ℂ V, (∀ i x, rel i x → χ x = χ x0 → Yp i ≤ Z) → Y ≤ Z := by
  classical
  have hT : ∀ t, ∃ T : V →ₗ[ℂ] V, ∀ f, T (s f) = s (α t f) := fun t => by
    refine PiLin.exists_desc _ _ fun u hu => ?_
    obtain ⟨K, hK⟩ := dir (insert z u.support)
    obtain ⟨act, a1, -⟩ := lev K (hK z (Finset.mem_insert_self _ _))
    have hm : ∀ f : u.support, mem K f := fun f => hK _ (Finset.mem_insert_of_mem f.2)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort] at hu ⊢
    have h0 : ∑ f : u.support, u f • (⟨s f, hEK K f (hm f)⟩ : EK K) = 0 := Subtype.ext (by
      rw [Submodule.coe_sum]; exact hu)
    have h3 := congrArg (fun F => (act t F : V)) h0
    simp only [map_sum, map_smul, map_zero, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h3
    rw [← h3]
    exact Finset.sum_congr rfl fun f _ => by rw [a1 t f (hm f)]
  choose T hT using hT
  let E := Submodule.span ℂ (Set.range s)
  have hE : ∀ f, s f ∈ E := fun f => Submodule.subset_span ⟨f, rfl⟩
  let J := {j : I × X × Submodule ℂ V // j.2.2 ≤ Yp j.1 ⊓ E ∧ rel j.1 j.2.1 ∧ ∀ t, ∀ F ∈ j.2.2, T t F = χ j.2.1 t • F}
  have hsup : E = ⨆ j : J, j.1.2.2 := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun j => j.2.1.trans inf_le_right)
    rintro _ ⟨f, rfl⟩
    obtain ⟨K, hK⟩ := dir {z, f}
    obtain ⟨act, a1, a3, a4⟩ := lev K (hK z (by simp))
    have hle : EK K ≤ E := (hEK' K).trans (Submodule.span_mono (Set.image_subset_range _ _))
    have hsp : Submodule.span ℂ (s '' {f | mem K f}) ≤ EK K := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact hEK K y hy)
    have hact : ∀ t F (hF : F ∈ Submodule.span ℂ (s '' {f | mem K f})), T t F = act t ⟨F, hsp hF⟩ := fun t F hF => by
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨y, hy, rfl⟩ := hF
        exact (hT t y).trans (a1 t y hy).symm
      | zero => exact (map_zero _).trans (congrArg Subtype.val (map_zero (act t))).symm
      | add F F' hF hF' h h' =>
        rw [map_add, h, h']
        exact (congrArg Subtype.val (map_add (act t) ⟨F, hsp hF⟩ ⟨F', hsp hF'⟩)).symm
      | smul u F hF h =>
        rw [map_smul, h]
        exact (congrArg Subtype.val (map_smul (act t) u ⟨F, hsp hF⟩)).symm
    refine (show EK K ≤ ⨆ j : J, j.1.2.2 from ?_) (hEK K f (hK f (by simp)))
    refine a3.trans (iSup_le fun i => ?_)
    by_cases hY : Yp i ⊓ EK K = ⊥
    · rw [hY]; exact bot_le
    · obtain ⟨x, b1, b2⟩ := a4 i hY
      exact le_iSup (fun j : J => j.1.2.2) ⟨(i, x, Yp i ⊓ EK K), inf_le_inf_left _ hle, b1, fun t F hF => by
        rw [hact t F (hEK' K hF.2), b2 t ⟨F, hF.2⟩ hF.1]; rfl⟩
  obtain ⟨j0, Y, p, -, y1, y2, y3, y4, y5⟩ := PiLin.exists_proj (J := J) T π E
    (fun g => show E ≤ E.comap (π g) from Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩
      change π g (s f) ∈ E
      rw [← h1]
      exact hE _))
    (fun t g F hF => LinearMap.eqOn_span' (f := T t ∘ₗ π g) (g := π g ∘ₗ T t) (by
      rintro _ ⟨f, rfl⟩
      simp only [LinearMap.comp_apply]
      rw [← h1, hT, hT, h2, h1]) hF)
    (fun j => j.1.2.2) (fun j => χ j.1.2.1) (fun j => j.2.2.2) hsup (s z) (hE z) hz
  refine ⟨j0.1.1, j0.1.2.1, Y, p, j0.2.2.1, y1, y2, fun t f => ?_, fun g f => ?_, fun Z hZ => y5.trans (iSup_le fun j => ?_)⟩
  · rw [← hT, y3 t _ (hE f)]
  · rw [h1, y4 g _ (hE f)]
  · exact (j.1.2.1.trans inf_le_left).trans (hZ _ _ j.1.2.2.1 j.2)
