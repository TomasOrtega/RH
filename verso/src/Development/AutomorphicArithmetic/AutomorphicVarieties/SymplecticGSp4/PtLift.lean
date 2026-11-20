import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal C`. Use `letI : Field (C ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType K (C ⧸ m) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)`. Use `haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)`. Use `haveI : Algebra.IsIntegral K (C ⧸ m) := Algebra.IsIntegral.of_finite K _`.

Establish `hb : Function.Bijective (algebraMap K (C ⧸ m))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Conclude with `⟨((AlgEquiv.ofBijective (Algebra.ofId K (C ⧸ m)) hb).symm : (C ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m)⟩`.
-/
private theorem pt_of_ft {K C : Type} [Field K] [IsAlgClosed K] [CommRing C] [Algebra K C] [Nontrivial C]
    [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (C ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  haveI : Algebra.IsIntegral K (C ⧸ m) := Algebra.IsIntegral.of_finite K _
  have hb : Function.Bijective (algebraMap K (C ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨((AlgEquiv.ofBijective (Algebra.ofId K (C ⧸ m)) hb).symm : (C ⧸ m) →ₐ[K] K).comp
    (Ideal.Quotient.mkₐ K m)⟩

/- English proof (translation)
Set `f : TensorProduct A K B →ₗ[A] K` to `TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)`. Establish `hf : f 1 = 1`. Rewrite using `[Algebra.TensorProduct.one_def]`. Simplify using `[f, h]`. Use `haveI : Nontrivial (TensorProduct A K B) := by`.

Use `⟨⟨1, 0, fun h0 => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `congrArg f h0`. Rewrite `h1` using `[hf, map_zero]`. Conclude with `one_ne_zero h1`. Use `haveI : Algebra.FiniteType K (TensorProduct A K B) := Algebra.FiniteType.baseChange K`.

Take `⟨φ⟩` from `pt_of_ft (K := K) (C := TensorProduct A K B)`. Conclude with `⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩`.
-/
private theorem pt_of_lin {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra A B]
    [Algebra A K] [Algebra.FiniteType A B] (ρ : B →ₗ[A] K) (h : ρ 1 = 1) : Nonempty (B →ₐ[A] K) := by
  classical
  let f : TensorProduct A K B →ₗ[A] K := TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)
  have hf : f 1 = 1 := by
    rw [Algebra.TensorProduct.one_def]
    simp [f, h]
  haveI : Nontrivial (TensorProduct A K B) := by
    refine ⟨⟨1, 0, fun h0 => ?_⟩⟩
    have h1 := congrArg f h0
    rw [hf, map_zero] at h1
    exact one_ne_zero h1
  haveI : Algebra.FiniteType K (TensorProduct A K B) := Algebra.FiniteType.baseChange K
  obtain ⟨φ⟩ := pt_of_ft (K := K) (C := TensorProduct A K B)
  exact ⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

/- English proof (translation)
Use `letI : Algebra A B := φ.toRingHom.toAlgebra`. Use `letI : Algebra A K := x.toRingHom.toAlgebra`. Establish `hwd : ∀ f g, φ f = φ g → x f = x g` using `fun f g hfg => by`. Establish `h0` using `hk (f - g) (by rw [map_sub, hfg, sub_self])`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Then use the resulting hypothesis.

Use `choose pre hpre using hr`. Establish `hO : ∀ r : O, algebraMap O B r = algebraMap A B (algebraMap O A r)` using `fun r => by show algebraMap O B r = φ (algebraMap O A r)`. Rewrite using `[AlgHom.commutes]`. Set `ρ : B →ₗ[A] K` to `{ toFun := fun t => x (pre t) map_add' := fun t u => by`. Rewrite using `[← map_add]`.

Apply `hwd` to reduce the goal to its premises. Rewrite using `[map_add, hpre, hpre, hpre, map_add]`. Use the proof step `map_smul' := fun a t => by show x (pre (a • t)) = x a * x (pre t)`. Rewrite using `[← map_mul]`. Apply `hwd` to reduce the goal to its premises.

Rewrite using `[hpre, map_mul, hpre, Algebra.smul_def]`. Conclude with `hP a t }`. Establish `h1' : ρ 1 = 1` using `by show x (pre 1) = 1`. Rewrite using `[← map_one x]`. Apply `hwd` to reduce the goal to its premises.

Rewrite using `[hpre, h1, map_one]`. Use `haveI : Algebra.FiniteType A B := by`. Use `⟨⟨hs.toFinset, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce and unpack `b -`.

Establish `hb : b ∈ Algebra.adjoin O (Set.range φ ∪ s)`. Rewrite using `[hg]`. Discharge the goal by the elementary cases of `trivial`. Rewrite using `[Set.Finite.coe_toFinset]`. Proceed by induction on `hb using Algebra.adjoin_induction with`.

Consider the case `mem y hy`. Break down `hy with ⟨f, rfl⟩ | hy` into its components or cases. Conclude with `Subalgebra.algebraMap_mem _ f`. Conclude with `Algebra.subset_adjoin hy`. Consider the case `algebraMap r`.

Rewrite using `[hO]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Consider the case `add y z _ _ hy hz => exact add_mem hy hz`. Consider the case `mul y z _ _ hy hz => exact mul_mem hy hz`. Take `⟨ψ⟩` from `pt_of_lin ρ h1'`.

Use `⟨{ toRingHom := ψ.toRingHom, commutes' := fun r => ?_ }, ?_⟩` and prove the remaining obligations. Use `show ψ (algebraMap O B r) = algebraMap O K r`. Rewrite using `[hO, ψ.commutes]`. Conclude with `x.commutes r`. Use extensionality with `f`.

Conclude with `ψ.commutes f`.
-/
private theorem ext_of_proj {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra O A] [Algebra O B] [Algebra O K] (φ : A →ₐ[O] B) (x : A →ₐ[O] K) (hk : ∀ f, φ f = 0 → x f = 0)
    (P : B →+ B) (hP : ∀ f s, P (φ f * s) = φ f * P s) (hr : ∀ s, ∃ f, φ f = P s) (h1 : P 1 = 1)
    (s : Set B) (hs : s.Finite) (hg : Algebra.adjoin O (Set.range φ ∪ s) = ⊤) :
    ∃ ξ : B →ₐ[O] K, ξ.comp φ = x := by
  classical
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := x.toRingHom.toAlgebra
  have hwd : ∀ f g, φ f = φ g → x f = x g := fun f g hfg => by
    have h0 := hk (f - g) (by rw [map_sub, hfg, sub_self])
    rwa [map_sub, sub_eq_zero] at h0
  choose pre hpre using hr
  have hO : ∀ r : O, algebraMap O B r = algebraMap A B (algebraMap O A r) := fun r => by
    show algebraMap O B r = φ (algebraMap O A r)
    rw [AlgHom.commutes]
  let ρ : B →ₗ[A] K :=
    { toFun := fun t => x (pre t)
      map_add' := fun t u => by
        rw [← map_add]
        apply hwd
        rw [map_add, hpre, hpre, hpre, map_add]
      map_smul' := fun a t => by
        show x (pre (a • t)) = x a * x (pre t)
        rw [← map_mul]
        apply hwd
        rw [hpre, map_mul, hpre, Algebra.smul_def]
        exact hP a t }
  have h1' : ρ 1 = 1 := by
    show x (pre 1) = 1
    rw [← map_one x]
    apply hwd
    rw [hpre, h1, map_one]
  haveI : Algebra.FiniteType A B := by
    refine ⟨⟨hs.toFinset, ?_⟩⟩
    rw [eq_top_iff]
    rintro b -
    have hb : b ∈ Algebra.adjoin O (Set.range φ ∪ s) := by
      rw [hg]
      trivial
    rw [Set.Finite.coe_toFinset]
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨f, rfl⟩ | hy
      · exact Subalgebra.algebraMap_mem _ f
      · exact Algebra.subset_adjoin hy
    | algebraMap r =>
      rw [hO]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  obtain ⟨ψ⟩ := pt_of_lin ρ h1'
  refine ⟨{ toRingHom := ψ.toRingHom, commutes' := fun r => ?_ }, ?_⟩
  · show ψ (algebraMap O B r) = algebraMap O K r
    rw [hO, ψ.commutes]
    exact x.commutes r
  · ext f
    exact ψ.commutes f

/- English proof (translation)
Set `L` to `DFinsupp.lsum ℕ (fun i => (𝒜 i).subtype)`. Set `Q` to `DFinsupp.lsum ℕ (fun i => if p i then (𝒜 i).subtype else (0 : 𝒜 i →ₗ[O] S))`. Establish `hL : Function.Injective L` using `h.dfinsupp_lsum_injective`. Set `P : S → S` to `fun t => if ht : ∃ y, L y = t then Q ht.choose else 0`. Establish `hP : ∀ y, P (L y) = Q y` using `fun y => by`.

Establish `ht : ∃ y', L y' = L y` using `⟨y, rfl⟩`. Use `show (if ht : ∃ y', L y' = L y then Q ht.choose else 0) = Q y`. Rewrite using `[dif_pos ht, hL ht.choose_spec]`. Establish `hmem : ∀ a ∈ ⨆ j, 𝒜 j, ∃ y, L y = a` using `fun a ha => by`. Rewrite `ha` using `[Submodule.iSup_eq_range_dfinsupp_lsum]`.

Conclude with `LinearMap.mem_range.1 ha`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `hP 0`. Rewrite `h0` using `[map_zero, map_zero]`. Then use the resulting hypothesis. Introduce `a ha b hb`.

Take `⟨ya, rfl⟩` from `hmem a ha`. Take `⟨yb, rfl⟩` from `hmem b hb`. Rewrite using `[← map_add, hP, hP, hP, map_add]`. Introduce `j a ha`. Establish `e : L (DFinsupp.single j ⟨a, ha⟩) = a`.

Simplify using `[L]`. Use `conv_lhs => rw [← e]`. Rewrite using `[hP]`. Simplify using `only [Q, DFinsupp.lsum_single]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem exists_proj {O S X : Type} [CommRing O] [AddCommGroup S] [Module O S] (𝒜 : X → Submodule O S)
    (h : iSupIndep 𝒜) (p : X → Prop) [DecidablePred p] :
    ∃ P : S → S, P 0 = 0 ∧ (∀ a ∈ ⨆ j, 𝒜 j, ∀ b ∈ ⨆ j, 𝒜 j, P (a + b) = P a + P b) ∧
      ∀ j, ∀ a ∈ 𝒜 j, P a = if p j then a else 0 := by
  classical
  let L := DFinsupp.lsum ℕ (fun i => (𝒜 i).subtype)
  let Q := DFinsupp.lsum ℕ (fun i => if p i then (𝒜 i).subtype else (0 : 𝒜 i →ₗ[O] S))
  have hL : Function.Injective L := h.dfinsupp_lsum_injective
  let P : S → S := fun t => if ht : ∃ y, L y = t then Q ht.choose else 0
  have hP : ∀ y, P (L y) = Q y := fun y => by
    have ht : ∃ y', L y' = L y := ⟨y, rfl⟩
    show (if ht : ∃ y', L y' = L y then Q ht.choose else 0) = Q y
    rw [dif_pos ht, hL ht.choose_spec]
  have hmem : ∀ a ∈ ⨆ j, 𝒜 j, ∃ y, L y = a := fun a ha => by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum] at ha
    exact LinearMap.mem_range.1 ha
  refine ⟨P, ?_, ?_, ?_⟩
  · have h0 := hP 0
    rwa [map_zero, map_zero] at h0
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := hmem a ha
    obtain ⟨yb, rfl⟩ := hmem b hb
    rw [← map_add, hP, hP, hP, map_add]
  · intro j a ha
    have e : L (DFinsupp.single j ⟨a, ha⟩) = a := by
      simp [L]
    conv_lhs => rw [← e]
    rw [hP]
    simp only [Q, DFinsupp.lsum_single]
    split_ifs <;> simp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD M x hx`. Take `⟨hind, ⟨s, hs1, hs2⟩, -⟩` from `sInternal D hD M`. Take `⟨hk1, hk2, -⟩` from `kerA D hD M`. Take `⟨P, hP0, hPadd, hPj⟩` from `exists_proj M.sPart hind (fun j : ℤ × ℤ => j.1 = 0)`. Establish `hz0 : ((M.toSS 0 : M.SS) : M.S) = 0`.

Establish `e0 : M.toSS 0 = 0` using `M.toSS.map_zero`. Rewrite using `[e0]`. Both sides reduce to the same expression. Establish `hPS : ∀ y ∈ ⨆ j, M.sPart j, P y ∈ ⨆ j, M.sPart j ∧ ∃ f : M.A, (M.toSS f : M.S) = P y`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.iSup_induction' with`. Consider the case `mem j y hy`. Rewrite using `[hPj j y hy]`. Use `split_ifs with hj`. Use `⟨Submodule.mem_iSup_of_mem j hy, ?_⟩` and prove the remaining obligations.

Take `⟨j1, j2⟩` from `j`. Simplify using `only at hj`. Substitute `hj` using the available equality. Take `⟨f, -, hf⟩` from `hk2 j2 ⟨y, M.sPart_le hy⟩ hy`. Conclude with `⟨f, congrArg Subtype.val hf⟩`.

Conclude with `⟨zero_mem _, 0, hz0⟩`. Consider the case `zero`. Rewrite using `[hP0]`. Conclude with `⟨zero_mem _, 0, hz0⟩`. Consider the case `add a b ha hb iha ihb`.

Rewrite using `[hPadd a ha b hb]`. Take `⟨h1, f1, hf1⟩` from `iha`. Take `⟨h2, f2, hf2⟩` from `ihb`. Use `⟨add_mem h1 h2, f1 + f2, ?_⟩` and prove the remaining obligations. Establish `e : M.toSS (f1 + f2) = M.toSS f1 + M.toSS f2` using `M.toSS.map_add f1 f2`.

Rewrite using `[← hf1, ← hf2, e]`. Both sides reduce to the same expression. Establish `hπm : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, M.π g * y ∈ ⨆ j, M.sPart j` using `fun g hg y hy => M.SS.mul_mem (M.π_mem ⟨g, hg⟩) hy`. Establish `hPmul : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, P (M.π g * y) = M.π g * P y`. Introduce `g hg`.

Proceed by induction on `hg using Submodule.iSup_induction' with`. Consider the case `mem n g hg`. Introduce `y hy`. Establish `hg' : g ∈ ⨆ n, M.aPart n` using `Submodule.mem_iSup_of_mem n hg`. Proceed by induction on `hy using Submodule.iSup_induction' with`.

Consider the case `mem j y hy`. Establish `hπ : M.π g ∈ M.sPart (0, n)` using `Submodule.mem_map_of_mem (f := M.π.toLinearMap) hg`. Establish `hgy : M.π g * y ∈ M.sPart ((0, n) + j)` using `SetLike.GradedMul.mul_mem hπ hy`. Rewrite using `[hPj _ _ hgy, hPj _ _ hy]`. Simplify using `only [Prod.fst_add, zero_add]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `zero => rw [mul_zero, hP0, mul_zero]`. Consider the case `add a b ha hb iha ihb`. Rewrite using `[mul_add, hPadd _ (hπm g hg' a ha) _ (hπm g hg' b hb), iha, ihb, hPadd a ha b hb, mul_add]`. Consider the case `zero`.

Introduce `y hy`. Establish `e0 : M.π 0 = 0` using `M.π.map_zero`. Rewrite using `[e0, zero_mul, hP0, zero_mul]`. Consider the case `add g h hg hh ihg ihh`. Introduce `y hy`.

Establish `e : M.π (g + h) = M.π g + M.π h` using `M.π.map_add g h`. Rewrite using `[e, add_mul, hPadd _ (hπm g hg y hy) _ (hπm h hh y hy), ihg y hy, ihh y hy, add_mul]`. Set `P' : M.SS →+ M.SS` to `{ toFun := fun y => ⟨P y.1, (hPS y.1 y.2).1⟩ map_zero' := Subtype.ext hP0 map_add' := fun a b => Subtype.ext (hPadd _ a.2 _ b.2) }`. Establish `h1P : P 1 = 1`. Establish `h1` using `hPj 0 1 SetLike.GradedOne.one_mem`.

Simplify using `using h1`. Set `s' : Set M.SS` to `Subtype.val ⁻¹' (s : Set M.S)`. Establish `hs' : s'.Finite` using `s.finite_toSet.preimage Subtype.val_injective.injOn`. Establish `hgen : Algebra.adjoin c.O (Set.range M.toSS ∪ s') = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce and unpack `y -`. Establish `key : Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) ≤ (Algebra.adjoin c.O (Set.range M.toSS ∪ s')).map M.SS.val`. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `z (hz | hz)`. Take `⟨f, -, hf⟩` from `hk2 0 ⟨z, M.sPart_le hz⟩ hz`.

Conclude with `Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hz⟩, Algebra.subset_adjoin (Or.inl ⟨f, hf⟩), rfl⟩`. Take `⟨w, hw⟩` from `hs1 z hz`. Conclude with `Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hw⟩, Algebra.subset_adjoin (Or.inr hz), rfl⟩`. Establish `hy : (y : M.S) ∈ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S))`. Rewrite using `[hs2]`.

Conclude with `y.2`. Take `⟨z, hz, hzy⟩` from `Subalgebra.mem_map.1 (key hy)`. Establish `hzy' : z = y` using `Subtype.ext hzy`. Rewrite using `[← hzy']`. Conclude with `hz`.

Conclude with `ext_of_proj M.toSS x (fun f hf => hx f ((hk1 f).1 hf)) P' (fun f y => Subtype.ext (hPmul f.1 f.2 y.1 y.2)) (fun y => ⟨(hPS y.1 y.2).2.choose, Subtype.ext (hPS y.1 y.2).2.choose_spec⟩) (Subtype.ext h1P) s' hs' hgen`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLift :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → ∃ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ.comp M.toSS = x := by
  intro Ω _ _ _ l _ c D hD M x hx
  obtain ⟨hind, ⟨s, hs1, hs2⟩, -⟩ := sInternal D hD M
  obtain ⟨hk1, hk2, -⟩ := kerA D hD M
  obtain ⟨P, hP0, hPadd, hPj⟩ := exists_proj M.sPart hind (fun j : ℤ × ℤ => j.1 = 0)
  have hz0 : ((M.toSS 0 : M.SS) : M.S) = 0 := by
    have e0 : M.toSS 0 = 0 := M.toSS.map_zero
    rw [e0]
    rfl
  have hPS : ∀ y ∈ ⨆ j, M.sPart j, P y ∈ ⨆ j, M.sPart j ∧ ∃ f : M.A, (M.toSS f : M.S) = P y := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem j y hy =>
      rw [hPj j y hy]
      split_ifs with hj
      · refine ⟨Submodule.mem_iSup_of_mem j hy, ?_⟩
        obtain ⟨j1, j2⟩ := j
        simp only at hj
        subst hj
        obtain ⟨f, -, hf⟩ := hk2 j2 ⟨y, M.sPart_le hy⟩ hy
        exact ⟨f, congrArg Subtype.val hf⟩
      · exact ⟨zero_mem _, 0, hz0⟩
    | zero =>
      rw [hP0]
      exact ⟨zero_mem _, 0, hz0⟩
    | add a b ha hb iha ihb =>
      rw [hPadd a ha b hb]
      obtain ⟨h1, f1, hf1⟩ := iha
      obtain ⟨h2, f2, hf2⟩ := ihb
      refine ⟨add_mem h1 h2, f1 + f2, ?_⟩
      have e : M.toSS (f1 + f2) = M.toSS f1 + M.toSS f2 := M.toSS.map_add f1 f2
      rw [← hf1, ← hf2, e]
      rfl
  have hπm : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, M.π g * y ∈ ⨆ j, M.sPart j :=
    fun g hg y hy => M.SS.mul_mem (M.π_mem ⟨g, hg⟩) hy
  have hPmul : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, P (M.π g * y) = M.π g * P y := by
    intro g hg
    induction hg using Submodule.iSup_induction' with
    | mem n g hg =>
      intro y hy
      have hg' : g ∈ ⨆ n, M.aPart n := Submodule.mem_iSup_of_mem n hg
      induction hy using Submodule.iSup_induction' with
      | mem j y hy =>
        have hπ : M.π g ∈ M.sPart (0, n) := Submodule.mem_map_of_mem (f := M.π.toLinearMap) hg
        have hgy : M.π g * y ∈ M.sPart ((0, n) + j) := SetLike.GradedMul.mul_mem hπ hy
        rw [hPj _ _ hgy, hPj _ _ hy]
        simp only [Prod.fst_add, zero_add]
        split_ifs <;> simp
      | zero => rw [mul_zero, hP0, mul_zero]
      | add a b ha hb iha ihb =>
        rw [mul_add, hPadd _ (hπm g hg' a ha) _ (hπm g hg' b hb), iha, ihb, hPadd a ha b hb, mul_add]
    | zero =>
      intro y hy
      have e0 : M.π 0 = 0 := M.π.map_zero
      rw [e0, zero_mul, hP0, zero_mul]
    | add g h hg hh ihg ihh =>
      intro y hy
      have e : M.π (g + h) = M.π g + M.π h := M.π.map_add g h
      rw [e, add_mul, hPadd _ (hπm g hg y hy) _ (hπm h hh y hy), ihg y hy, ihh y hy, add_mul]
  let P' : M.SS →+ M.SS :=
    { toFun := fun y => ⟨P y.1, (hPS y.1 y.2).1⟩
      map_zero' := Subtype.ext hP0
      map_add' := fun a b => Subtype.ext (hPadd _ a.2 _ b.2) }
  have h1P : P 1 = 1 := by
    have h1 := hPj 0 1 SetLike.GradedOne.one_mem
    simpa using h1
  let s' : Set M.SS := Subtype.val ⁻¹' (s : Set M.S)
  have hs' : s'.Finite := s.finite_toSet.preimage Subtype.val_injective.injOn
  have hgen : Algebra.adjoin c.O (Set.range M.toSS ∪ s') = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have key : Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) ≤
        (Algebra.adjoin c.O (Set.range M.toSS ∪ s')).map M.SS.val := by
      apply Algebra.adjoin_le
      rintro z (hz | hz)
      · obtain ⟨f, -, hf⟩ := hk2 0 ⟨z, M.sPart_le hz⟩ hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hz⟩, Algebra.subset_adjoin (Or.inl ⟨f, hf⟩), rfl⟩
      · obtain ⟨w, hw⟩ := hs1 z hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hw⟩, Algebra.subset_adjoin (Or.inr hz), rfl⟩
    have hy : (y : M.S) ∈ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) := by
      rw [hs2]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.1 (key hy)
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  exact ext_of_proj M.toSS x (fun f hf => hx f ((hk1 f).1 hf)) P'
    (fun f y => Subtype.ext (hPmul f.1 f.2 y.1 y.2))
    (fun y => ⟨(hPS y.1 y.2).2.choose, Subtype.ext (hPS y.1 y.2).2.choose_spec⟩)
    (Subtype.ext h1P) s' hs' hgen
