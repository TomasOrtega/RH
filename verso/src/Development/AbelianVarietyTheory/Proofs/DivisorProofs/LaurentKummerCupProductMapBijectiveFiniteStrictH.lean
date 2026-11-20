import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentMapIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyProdRingProjectionsBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraStrictlyHenselianInductionStatement
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep

noncomputable section
namespace GlobalTheory.EtC.LaurentMapPullbackBijective

/- English proof (translation)
Unfold `laurentMap`. Simplify using the standard rewrite rules.
-/
theorem laurentMap_coeff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (p : LaurentPolynomial A) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  unfold laurentMap
  simp

/- English proof (translation)
The claim follows from `AddMonoidAlgebra.mapRingHom_id`.
-/
theorem laurentMap_id (A : Type) [CommRing A] : laurentMap (RingHom.id A) = RingHom.id _ :=
  AddMonoidAlgebra.mapRingHom_id

/- English proof (translation)
Simplify using `[spMap]`.
-/
theorem spMap_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 (sp A) := by
  simp [spMap]

/- English proof (translation)
Use `Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap g) (tw q i) n, fun x => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← GmPhiNat.pull_spMap_comp, hgf, spMap_id, pull_id]`. Rewrite using `[← GmPhiNat.pull_spMap_comp, hfg, spMap_id, pull_id]`.
-/
theorem pull_bijective_of_inverse (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (g : B →+* A)
    (hgf : g.comp f = RingHom.id A) (hfg : f.comp g = RingHom.id B) (n i : ℤ) :
    Function.Bijective (pull _ (spMap f) (tw q i) n) := by
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap g) (tw q i) n, fun x => ?_, fun y => ?_⟩
  · rw [← GmPhiNat.pull_spMap_comp, hgf, spMap_id, pull_id]
  · rw [← GmPhiNat.pull_spMap_comp, hfg, spMap_id, pull_id]

/- English proof (translation)
Establish `hb` using `GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T T n i`. Establish `hfs : RingHom.fst T T = RingHom.snd T T` using `RingHom.ext fun _ => Subsingleton.elim _ _`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hb.2 (a, b)`. Establish `h1` using `congrArg Prod.fst hx`.

Establish `h2` using `congrArg Prod.snd hx`. Simplify using `only at h1 h2`. Rewrite `h1` using `[hfs]`. Conclude with `h1.symm.trans h2`.
-/
theorem ht_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (n i : ℤ) :
    Subsingleton (Ht q (sp T) n i) := by
  have hb := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T T n i
  have hfs : RingHom.fst T T = RingHom.snd T T := RingHom.ext fun _ => Subsingleton.elim _ _
  refine ⟨fun a b => ?_⟩
  obtain ⟨x, hx⟩ := hb.2 (a, b)
  have h1 := congrArg Prod.fst hx
  have h2 := congrArg Prod.snd hx
  simp only at h1 h2
  rw [hfs] at h1
  exact h1.symm.trans h2

/- English proof (translation)
Use `subsingleton_of_zero_eq_one ?_` and prove the remaining obligations. Rewrite using `[← map_zero (LaurentPolynomial.C : T →+* LaurentPolynomial T), ← map_one (LaurentPolynomial.C : T →+* LaurentPolynomial T), Subsingleton.elim (0 : T) 1]`.
-/
theorem laurent_subsingleton (T : Type) [CommRing T] [Subsingleton T] : Subsingleton (LaurentPolynomial T) := by
  refine subsingleton_of_zero_eq_one ?_
  rw [← map_zero (LaurentPolynomial.C : T →+* LaurentPolynomial T), ← map_one (LaurentPolynomial.C : T →+* LaurentPolynomial T),
    Subsingleton.elim (0 : T) 1]

/- English proof (translation)
Use `haveI := ht_subsingleton q T 0 (i - 1)`. Use `haveI := laurent_subsingleton T`. Use `haveI := ht_subsingleton q (LaurentPolynomial T) 1 i`. Conclude with `⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩`.
-/
theorem gmPhi_bijective_of_subsingleton (q : ℕ) (T : Type) [CommRing T] [Subsingleton T] (i : ℤ) :
    Function.Bijective (gmPhi q T i) := by
  haveI := ht_subsingleton q T 0 (i - 1)
  haveI := laurent_subsingleton T
  haveI := ht_subsingleton q (LaurentPolynomial T) 1 i
  exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/- English proof (translation)
Establish `hcomm : (gmPhi q T' i) ∘ (pull _ (spMap (e : T →+* T')) _ 0) = (pull _ (spMap (laurentMap (e : T →+* T'))) _ 1) ∘ (gmPhi q T i)`. Use function extensionality and compare the values at `fun a => (gmPhi_nat h6 q (e : T →+* T') hq i a).symm`. Establish `hgf : (e.symm : T' →+* T).comp (e : T →+* T') = RingHom.id T` using `by ext; simp`. Establish `hfg : (e : T →+* T').comp (e.symm : T' →+* T) = RingHom.id T'` using `by ext; simp`. Establish `hpull` using `pull_bijective_of_inverse q (e : T →+* T') (e.symm : T' →+* T) hgf hfg 0 (i - 1)`.

Establish `hpullL` using `pull_bijective_of_inverse q (laurentMap (e : T →+* T')) (laurentMap (e.symm : T' →+* T)) (by rw [← GmPhiNat.laurentMap_comp, hgf, laurentMap_id]) (by rw [← GmPhiNat.laurentMap_comp, hfg, laurentMap_id]) 1 i`. Rewrite using `[← Function.Bijective.of_comp_iff _ hpull, hcomm]`. Conclude with `hpullL.comp h`.
-/
theorem gmPhi_bijective_of_equiv (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {T T' : Type} [CommRing T] [CommRing T']
    (e : T ≃+* T') (hq : IsUnit (q : T)) (i : ℤ) (h : Function.Bijective (gmPhi q T i)) :
    Function.Bijective (gmPhi q T' i) := by
  have hcomm : (gmPhi q T' i) ∘ (pull _ (spMap (e : T →+* T')) _ 0) =
      (pull _ (spMap (laurentMap (e : T →+* T'))) _ 1) ∘ (gmPhi q T i) :=
    funext fun a => (gmPhi_nat h6 q (e : T →+* T') hq i a).symm
  have hgf : (e.symm : T' →+* T).comp (e : T →+* T') = RingHom.id T := by ext; simp
  have hfg : (e : T →+* T').comp (e.symm : T' →+* T) = RingHom.id T' := by ext; simp
  have hpull := pull_bijective_of_inverse q (e : T →+* T') (e.symm : T' →+* T) hgf hfg 0 (i - 1)
  have hpullL := pull_bijective_of_inverse q (laurentMap (e : T →+* T')) (laurentMap (e.symm : T' →+* T))
    (by rw [← GmPhiNat.laurentMap_comp, hgf, laurentMap_id])
    (by rw [← GmPhiNat.laurentMap_comp, hfg, laurentMap_id]) 1 i
  rw [← Function.Bijective.of_comp_iff _ hpull, hcomm]
  exact hpullL.comp h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `p p' h`. Establish `h1` using `congrArg Prod.fst h`. Establish `h2` using `congrArg Prod.snd h`. Simplify using `only [RingHom.prod_apply] at h1 h2`.

Apply `AddMonoidAlgebra.ext` to reduce the goal to its premises. Use `Finsupp.ext fun n => ?_` and prove the remaining obligations. Establish `e1` using `congrArg (fun r => r.coeff n) h1`. Establish `e2` using `congrArg (fun r => r.coeff n) h2`. Simplify using `only [laurentMap_coeff, RingHom.coe_fst, RingHom.coe_snd] at e1 e2`.

Conclude with `Prod.ext e1 e2`. Introduce and unpack `⟨p₁, p₂⟩`. Use `⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk (by simp) p₁.coeff p₂.coeff), ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.prod_apply]`. Use `Prod.ext (AddMonoidAlgebra.ext ?_) (AddMonoidAlgebra.ext ?_)` and prove the remaining obligations.

Use extensionality with `n`. Simplify using `[laurentMap_coeff]`. Use extensionality with `n`. Simplify using `[laurentMap_coeff]`.
-/
theorem laurentProd_bijective (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂] :
    Function.Bijective ((laurentMap (RingHom.fst T₁ T₂)).prod (laurentMap (RingHom.snd T₁ T₂))) := by
  constructor
  · intro p p' h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [RingHom.prod_apply] at h1 h2
    apply AddMonoidAlgebra.ext
    refine Finsupp.ext fun n => ?_
    have e1 := congrArg (fun r => r.coeff n) h1
    have e2 := congrArg (fun r => r.coeff n) h2
    simp only [laurentMap_coeff, RingHom.coe_fst, RingHom.coe_snd] at e1 e2
    exact Prod.ext e1 e2
  · rintro ⟨p₁, p₂⟩
    refine ⟨AddMonoidAlgebra.ofCoeff (Finsupp.zipWith Prod.mk (by simp) p₁.coeff p₂.coeff), ?_⟩
    simp only [RingHom.prod_apply]
    refine Prod.ext (AddMonoidAlgebra.ext ?_) (AddMonoidAlgebra.ext ?_)
    · ext n; simp [laurentMap_coeff]
    · ext n; simp [laurentMap_coeff]

/- English proof (translation)
Use `set f₁ := RingHom.fst T₁ T₂`. Use `set f₂ := RingHom.snd T₁ T₂`. Use `set ψ := (laurentMap f₁).prod (laurentMap f₂)`. Establish `hα` using `GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T₁ T₂ 0 (i - 1)`. Establish `hγ` using `GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (LaurentPolynomial T₁) (LaurentPolynomial T₂) 1 i`.

Establish `hψ : Function.Bijective ψ` using `laurentProd_bijective T₁ T₂`. Set `e` to `RingEquiv.ofBijective ψ hψ`. Establish `hgf : e.symm.toRingHom.comp e.toRingHom = RingHom.id _` using `RingHom.ext fun x => e.symm_apply_apply x`. Establish `hfg : e.toRingHom.comp e.symm.toRingHom = RingHom.id _` using `RingHom.ext fun x => e.apply_symm_apply x`. Establish `hψpull` using `pull_bijective_of_inverse q e.toRingHom e.symm.toRingHom hgf hfg 1 i`.

Establish `he : e.toRingHom = ψ` using `rfl`. Establish `hl₁ : laurentMap f₁ = (RingHom.fst _ _).comp ψ` using `rfl`. Establish `hl₂ : laurentMap f₂ = (RingHom.snd _ _).comp ψ` using `rfl`. Set `β` to `fun y : Ht q (sp (LaurentPolynomial (T₁ × T₂))) 1 i => (pull _ (spMap (laurentMap f₁)) _ 1 y, pull _ (spMap (laurentMap f₂)) _ 1 y)`. Establish `hβ : Function.Bijective β`.

Establish `: β = (fun x : Ht q (sp (LaurentPolynomial T₁ × LaurentPolynomial T₂)) 1 i => (pull _ (spMap (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x, pull _ (spMap (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x)) ∘ (pull _ (spMap ψ) _ 1)`. Use function extensionality and compare the values at `y`. Simplify using `only [β, Function.comp_apply, hl₁, hl₂, GmPhiNat.pull_spMap_comp]`. Rewrite using `[this]`. Rewrite `hψpull` using `[he]`.

Conclude with `hγ.comp hψpull`. Establish `hu₁ : IsUnit (q : T₁)` using `by simpa using hq.map f₁`. Establish `hu₂ : IsUnit (q : T₂)` using `by simpa using hq.map f₂`. Establish `hcomm : β ∘ (gmPhi q (T₁ × T₂) i) = (Prod.map (gmPhi q T₁ i) (gmPhi q T₂ i)) ∘ (fun x : Ht q (sp (T₁ × T₂)) 0 (i - 1) => (pull _ (spMap f₁) _ 0 x, pull _ (spMap f₂) _ 0 x))`. Use function extensionality and compare the values at `a`.

Simplify using `only [β, Function.comp_apply, Prod.map_apply]`. Rewrite using `[gmPhi_nat h6 q f₁ hq i a, gmPhi_nat h6 q f₂ hq i a]`. Rewrite using `[← Function.Bijective.of_comp_iff' hβ, hcomm]`. Conclude with `(h₁.prodMap h₂).comp hα`.
-/
theorem gmPhi_bijective_prod (h6 : DivisorNaturality) (q : ℕ) [NeZero q] (T₁ T₂ : Type) [CommRing T₁] [CommRing T₂]
    (hq : IsUnit (q : T₁ × T₂)) (i : ℤ) (h₁ : Function.Bijective (gmPhi q T₁ i))
    (h₂ : Function.Bijective (gmPhi q T₂ i)) : Function.Bijective (gmPhi q (T₁ × T₂) i) := by
  set f₁ := RingHom.fst T₁ T₂
  set f₂ := RingHom.snd T₁ T₂
  set ψ := (laurentMap f₁).prod (laurentMap f₂)
  have hα := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q T₁ T₂ 0 (i - 1)
  have hγ := GlobalTheory.T.etaleCohomology_prod_ring_projections_bijective q (LaurentPolynomial T₁) (LaurentPolynomial T₂) 1 i
  have hψ : Function.Bijective ψ := laurentProd_bijective T₁ T₂
  let e := RingEquiv.ofBijective ψ hψ
  have hgf : e.symm.toRingHom.comp e.toRingHom = RingHom.id _ := RingHom.ext fun x => e.symm_apply_apply x
  have hfg : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := RingHom.ext fun x => e.apply_symm_apply x
  have hψpull := pull_bijective_of_inverse q e.toRingHom e.symm.toRingHom hgf hfg 1 i
  have he : e.toRingHom = ψ := rfl
  have hl₁ : laurentMap f₁ = (RingHom.fst _ _).comp ψ := rfl
  have hl₂ : laurentMap f₂ = (RingHom.snd _ _).comp ψ := rfl
  let β := fun y : Ht q (sp (LaurentPolynomial (T₁ × T₂))) 1 i =>
    (pull _ (spMap (laurentMap f₁)) _ 1 y, pull _ (spMap (laurentMap f₂)) _ 1 y)
  have hβ : Function.Bijective β := by
    have : β = (fun x : Ht q (sp (LaurentPolynomial T₁ × LaurentPolynomial T₂)) 1 i =>
        (pull _ (spMap (RingHom.fst (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x,
          pull _ (spMap (RingHom.snd (LaurentPolynomial T₁) (LaurentPolynomial T₂))) _ 1 x)) ∘
        (pull _ (spMap ψ) _ 1) := by
      funext y
      simp only [β, Function.comp_apply, hl₁, hl₂, GmPhiNat.pull_spMap_comp]
    rw [this]
    rw [he] at hψpull
    exact hγ.comp hψpull
  have hu₁ : IsUnit (q : T₁) := by simpa using hq.map f₁
  have hu₂ : IsUnit (q : T₂) := by simpa using hq.map f₂
  have hcomm : β ∘ (gmPhi q (T₁ × T₂) i) =
      (Prod.map (gmPhi q T₁ i) (gmPhi q T₂ i)) ∘
        (fun x : Ht q (sp (T₁ × T₂)) 0 (i - 1) => (pull _ (spMap f₁) _ 0 x, pull _ (spMap f₂) _ 0 x)) := by
    funext a
    simp only [β, Function.comp_apply, Prod.map_apply]
    rw [gmPhi_nat h6 q f₁ hq i a, gmPhi_nat h6 q f₂ hq i a]
  rw [← Function.Bijective.of_comp_iff' hβ, hcomm]
  exact (h₁.prodMap h₂).comp hα

end GlobalTheory.EtC.LaurentMapPullbackBijective

open GlobalTheory.EtC.LaurentMapPullbackBijective in

/- English proof (translation)
Introduce `q _ A _ hA hq T _ _ hT`. Establish `h6 : DivisorNaturality` using `GlobalTheory.T.cup_chern_kummer_pullback_naturality`. Establish `hunit : ∀ (S : Type) [CommRing S] [Algebra A S], IsUnit (q : S)` using `fun S _ _ => by`. Simplify using `using hq.map (algebraMap A S)`. Conclude with `GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun S _ _ => ∀ i : ℤ, Function.Bijective (gmPhi q S i)) (fun S S' _ _ _ _ e h i => gmPhi_bijective_of_equiv h6 q e.toRingEquiv (hunit S) i (h i)) (fun S _ _ _ i => gmPhi_bijective_of_subsingleton q S i) (fun S₁ S₂ _ _ …`.
-/
theorem GlobalTheory.EtC.GmStep.gmPhi_bijective_finite : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ (T : Type) [CommRing T] [Algebra A T], Module.Finite A T → ∀ i : ℤ, Function.Bijective (gmPhi q T i) := by
  intro q _ A _ hA hq T _ _ hT
  have h6 : DivisorNaturality := GlobalTheory.T.cup_chern_kummer_pullback_naturality
  have hunit : ∀ (S : Type) [CommRing S] [Algebra A S], IsUnit (q : S) := fun S _ _ => by
    simpa using hq.map (algebraMap A S)
  exact GlobalTheory.T.finiteAlgebra_strictlyHenselian_induction A hA (fun S _ _ => ∀ i : ℤ, Function.Bijective (gmPhi q S i))
    (fun S S' _ _ _ _ e h i => gmPhi_bijective_of_equiv h6 q e.toRingEquiv (hunit S) i (h i))
    (fun S _ _ _ i => gmPhi_bijective_of_subsingleton q S i)
    (fun S₁ S₂ _ _ _ _ _ _ h₁ h₂ i => gmPhi_bijective_prod h6 q S₁ S₂ (hunit (S₁ × S₂)) i (h₁ i) (h₂ i))
    (fun S _ _ _ hS i => GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian q S hS (hunit S) i)
    T hT
