import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobsonClosedPointsToolsInt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianSchemeProperClosureDataBasicProperties
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalCoordinates
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
namespace GlobalTheory.ZJ.FibreCoord

/- English proof (translation)
Use `haveI := AugCot.smooth_of_locally h`. Use `haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B`. Take `⟨e⟩` from `AugCot.nonempty_basis_of_locally χ h`. Use `choose t ht using fun i => (RingHom.ker χ).toCotangent_surjective (e i)`. Set `m` to `RingHom.ker χ`.

Set `J : Ideal B` to `Ideal.span (Set.range fun i => (t i : B))`. Establish `hle : m ≤ J ⊔ m • m`. Introduce `b hb`. Establish `h1 : AugCot.d χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0`. Rewrite using `[map_sub, map_sum]`.

Simplify using `only [map_smul, AugCot.d_coe]`. Use `e.sum_repr (AugCot.d χ b)` as an intermediate fact. Rewrite using `[sub_eq_zero]`. Use `conv_lhs => rw [← this]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [← ht i]`.

Rewrite `h1` using `[AugCot.d_eq_zero_iff]`. Establish `h2 : χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0`. Establish `hb' : χ b = 0` using `hb`. Establish `ht' : ∀ i, χ (t i) = 0` using `fun i => (t i).2`. Simplify using `[map_sum, hb', ht']`.

Rewrite `h1` using `[h2, map_zero, sub_zero, pow_two]`. Establish `h3 : ∑ i, e.repr (AugCot.d χ b) i • (t i : B) ∈ J` using `Ideal.sum_mem _ fun i _ => by`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`. Use `Ideal.add_mem _ (Ideal.mem_sup_left (T := m • m) h3) (Ideal.mem_sup_right (S := J) h1)` as an intermediate fact.

Simplify using `using this`. Take `⟨r, hr, hr'⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m (Submodule.map (Submodule.mkQ J) m) (Submodule.FG.map _ (IsNoetherian.noetherian m)) (by`. Rewrite using `[← Submodule.map_smul'', Submodule.map_le_iff_le_comap, Submodule.comap_map_mkQ]`. Conclude with `hle)`. Use `⟨fun i => t i, r, ?_, fun i => (t i).2, fun b hb => ?_⟩` and prove the remaining obligations.

Establish `: χ (r - 1) = 0` using `hr`. Rewrite `this` using `[map_sub, map_one, sub_eq_zero]`. Simplify using `[this]`. Use `hr' (Submodule.mkQ J b) (Submodule.mem_map_of_mem hb)` as an intermediate fact. Rewrite `this` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `this`.
-/
theorem exists_local_generators {K B : Type} [Field K] [CommRing B] [Algebra K B] {g : ℕ}
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B)) (χ : B →ₐ[K] K) :
    ∃ (t : Fin g → B) (s : B), χ s ≠ 0 ∧ (∀ i, χ (t i) = 0) ∧
      ∀ b, χ b = 0 → s * b ∈ Ideal.span (Set.range t) := by
  haveI := AugCot.smooth_of_locally h
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  obtain ⟨e⟩ := AugCot.nonempty_basis_of_locally χ h
  choose t ht using fun i => (RingHom.ker χ).toCotangent_surjective (e i)
  let m := RingHom.ker χ
  let J : Ideal B := Ideal.span (Set.range fun i => (t i : B))
  have hle : m ≤ J ⊔ m • m := by
    intro b hb
    have h1 : AugCot.d χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, AugCot.d_coe]
      have := e.sum_repr (AugCot.d χ b)
      rw [sub_eq_zero]
      conv_lhs => rw [← this]
      exact Finset.sum_congr rfl fun i _ => by rw [← ht i]
    rw [AugCot.d_eq_zero_iff] at h1
    have h2 : χ (b - ∑ i, e.repr (AugCot.d χ b) i • (t i : B)) = 0 := by
      have hb' : χ b = 0 := hb
      have ht' : ∀ i, χ (t i) = 0 := fun i => (t i).2
      simp [map_sum, hb', ht']
    rw [h2, map_zero, sub_zero, pow_two] at h1
    have h3 : ∑ i, e.repr (AugCot.d χ b) i • (t i : B) ∈ J :=
      Ideal.sum_mem _ fun i _ => by
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    have := Ideal.add_mem _ (Ideal.mem_sup_left (T := m • m) h3) (Ideal.mem_sup_right (S := J) h1)
    simpa using this
  obtain ⟨r, hr, hr'⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (Submodule.map (Submodule.mkQ J) m) (Submodule.FG.map _ (IsNoetherian.noetherian m)) (by
      rw [← Submodule.map_smul'', Submodule.map_le_iff_le_comap, Submodule.comap_map_mkQ]
      exact hle)
  refine ⟨fun i => t i, r, ?_, fun i => (t i).2, fun b hb => ?_⟩
  · have : χ (r - 1) = 0 := hr
    rw [map_sub, map_one, sub_eq_zero] at this
    simp [this]
  · have := hr' (Submodule.mkQ J b) (Submodule.mem_map_of_mem hb)
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
    exact this

/- English proof (translation)
Use `haveI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)`. Establish `h1 : nilradical T = Ideal.jacobson (nilradical T)` using `(IsJacobsonRing.out inferInstance (Ideal.radical_isRadical ⊥)).symm`. Rewrite using `[h1, Ideal.jacobson, Ideal.mem_sInf]`. Introduce and unpack `M ⟨-, hM⟩`. Use `letI := Ideal.Quotient.field M`.

Use `haveI : Module.Finite K (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ M)`. Set `e : T ⧸ M →ₐ[K] K` to `IsAlgClosed.lift`. Use `h (e.comp (Ideal.Quotient.mkₐ K M))` as an intermediate fact. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `(map_eq_zero_iff e e.toRingHom.injective).mp this`.
-/
theorem mem_nilradical_of_forall_algHom {K T : Type} [Field K] [IsAlgClosed K] [CommRing T] [Algebra K T]
    [Algebra.FiniteType K T] (a : T) (h : ∀ χ : T →ₐ[K] K, χ a = 0) : a ∈ nilradical T := by
  haveI : IsJacobsonRing T := isJacobsonRing_of_finiteType (A := K)
  have h1 : nilradical T = Ideal.jacobson (nilradical T) :=
    (IsJacobsonRing.out inferInstance (Ideal.radical_isRadical ⊥)).symm
  rw [h1, Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  letI := Ideal.Quotient.field M
  haveI : Module.Finite K (T ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (T ⧸ M)
  let e : T ⧸ M →ₐ[K] K := IsAlgClosed.lift
  have := h (e.comp (Ideal.Quotient.mkₐ K M))
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (map_eq_zero_iff e e.toRingHom.injective).mp this

open TensorProduct in

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `haveI : Algebra.FiniteType R S := hα`. Use `set P : Ideal R := RingHom.ker (ψ.comp α) with hP`. Use `haveI : P.IsPrime := RingHom.ker_isPrime _`. Use `haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _`.

Use `haveI : Finite (R ⧸ P) := Finite.of_injective _ (Ideal.quotientMap_injective (I := RingHom.ker ψ) (f := α))`. Use `haveI hPm : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)`. Establish `hmm : (RingHom.ker ψ).IsMaximal` using `Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)`. Use `letI := Ideal.Quotient.field P`. Set `Q : Ideal S` to `P.map (algebraMap R S)`.

Use `letI : Algebra (R ⧸ P) K := (RingHom.kerLift (ψ.comp α)).toAlgebra`. Use `haveI : Algebra.FiniteType (R ⧸ P) (S ⧸ Q) := Algebra.FiniteType.of_restrictScalars_finiteType R _ _`. Use `letI : Algebra (R ⧸ P) B := ((algebraMap K B).comp (algebraMap (R ⧸ P) K)).toAlgebra`. Use `haveI : IsScalarTower (R ⧸ P) K B := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hβ' : ∀ r, β (α r) = algebraMap K B (ψ (α r))` using `fun r => congr($hβ r)`.

Establish `hQβ : ∀ a ∈ Q, β a = 0`. Introduce `a ha`. Use `(show Q ≤ RingHom.ker β from Ideal.map_le_iff_le_comap.mpr fun r hr => ?_) ha` and prove the remaining obligations. Establish `hr' : ψ (α r) = 0` using `hr`. Express the relevant statement in the definitionally equal form `β (α r) = 0`.

Rewrite using `[hβ', hr', map_zero]`. Establish `hQψ : Q ≤ RingHom.ker ψ` using `Ideal.map_le_iff_le_comap.mpr fun r hr => hr`. Set `β' : S ⧸ Q →ₐ[R ⧸ P] B` to `{ Ideal.Quotient.lift Q β hQβ with commutes' := fun r => by`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Conclude with `hβ' r }`.

Set `φ : K ⊗[R ⧸ P] (S ⧸ Q) →ₐ[K] B` to `Algebra.TensorProduct.lift (Algebra.ofId K B) β' fun _ _ => Commute.all _ _`. Establish `hφ : ∀ a : S, φ (1 ⊗ₜ Ideal.Quotient.mk Q a) = β a` using `fun a => by`. Simplify using `[φ, β']`. Establish `hsurj : Function.Surjective φ`. Rewrite using `[← AlgHom.range_eq_top, eq_top_iff, ← hgen]`.

Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨_, hφ a⟩`. Establish `hker : RingHom.ker φ ≤ nilradical _`. Introduce `a ha`.

Use `mem_nilradical_of_forall_algHom (K := K) a fun χ' => ?_` and prove the remaining obligations. Set `ψ' : S →+* K` to `χ'.toRingHom.comp ((Algebra.TensorProduct.includeRight (R := R ⧸ P) (A := K) (B := S ⧸ Q)).toRingHom.comp (Ideal.Quotient.mk Q))`. Take `⟨χ, hχ⟩` from `hpt ψ' (by`. Use extensionality with `r`. Establish `: (1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r)) = algebraMap K _ (ψ (α r))`.

Express the relevant statement in the definitionally equal form `(1 : K) ⊗ₜ[R ⧸ P] (algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P r)) = (algebraMap (R ⧸ P) K (Ideal.Quotient.mk P r)) ⊗ₜ 1`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Express the relevant statement in the definitionally equal form `χ' ((1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r))) = ψ (α r)`. Rewrite using `[this, AlgHom.commutes]`. Use the proof step `rfl)`.

Establish `e : χ.comp φ = χ'`. Use extensionality with `b`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Express the relevant statement in the definitionally equal form `χ (φ (1 ⊗ₜ Ideal.Quotient.mk Q b)) = χ' (1 ⊗ₜ Ideal.Quotient.mk Q b)`. Rewrite using `[hφ]`.

Conclude with `congr($hχ b)`. Establish `ha' : φ a = 0` using `ha`. Rewrite using `[← e, AlgHom.comp_apply, ha', map_zero]`. Take `⟨χ, hχ⟩` from `hpt ψ rfl`. Establish `hχ' : ∀ a, χ (β a) = ψ a` using `fun a => congr($hχ a)`.

Use `haveI := AugCot.smooth_of_locally h`. Establish `hmem : ∀ a : S, Ideal.Quotient.mk Q a ∈ (RingHom.ker ψ).map (Ideal.Quotient.mk Q) ↔ a ∈ RingHom.ker ψ` using `fun a => by`. Rewrite using `[← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hQψ]`. Take `⟨u, s, hs, hu, hus⟩` from `GlobalTheory.LocalCoord.exists_local_coordinates (R ⧸ P) (S ⧸ Q) K B φ χ g ((RingHom.ker ψ).map (Ideal.Quotient.mk Q)) hsurj hker (fun a => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Rewrite using `[hmem, hφ, hχ', RingHom.mem_ker])`. Use the proof step `((Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hmm).resolve_left fun ht => hmm.ne_top (Ideal.eq_top_iff_one _ |>.mpr ((hmem 1).mp (ht ▸ trivial))))`. Use the proof step `(exists_local_generators h χ) (isReduced_of_smooth_of_isIntegrallyClosed K B)`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s`. Use `choose v hv using fun i => Ideal.Quotient.mk_surjective (u i)`.

Use `⟨v, s, fun h => hs ((hmem s).mpr h), fun i => (hmem _).mp (hv i ▸ hu i), fun a ha => ?_⟩` and prove the remaining obligations. Establish `h1` using `hus _ ((hmem a).mpr ha)`. Establish `h2 : Ideal.span (Set.range u) ⊔ nilradical (S ⧸ Q) = (Ideal.span (Set.range v) ⊔ Q.radical).map (Ideal.Quotient.mk Q)`. Rewrite using `[Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]), Ideal.map_quotient_self]`. Use `congr 3`.

Conclude with `funext fun i => (hv i).symm`. Rewrite `h1` using `[h2, ← map_mul, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_assoc, sup_eq_left.mpr (Ideal.le_radical (I := Q))]`. Conclude with `h1`.
-/
theorem exists_coords_ring {R S K B : Type} [CommRing R] [CommRing S] [Field K] [IsAlgClosed K] [CommRing B]
    [Algebra K B] {g : ℕ} (α : R →+* S) (hα : α.FiniteType) (ψ : S →+* K) [Finite (S ⧸ RingHom.ker ψ)]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B))
    (β : S →+* B) (hβ : β.comp α = (algebraMap K B).comp (ψ.comp α))
    (hgen : Algebra.adjoin K (Set.range β) = ⊤)
    (hpt : ∀ ψ' : S →+* K, ψ'.comp α = ψ.comp α → ∃ χ : B →ₐ[K] K, (χ : B →+* K).comp β = ψ') :
    ∃ (u : Fin g → S) (s : S), s ∉ RingHom.ker ψ ∧ (∀ i, u i ∈ RingHom.ker ψ) ∧
      ∀ a ∈ RingHom.ker ψ, s * a ∈ Ideal.span (Set.range u) ⊔ ((RingHom.ker (ψ.comp α)).map α).radical := by
  letI := α.toAlgebra
  haveI : Algebra.FiniteType R S := hα
  set P : Ideal R := RingHom.ker (ψ.comp α) with hP
  haveI : P.IsPrime := RingHom.ker_isPrime _
  haveI : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime _
  haveI : Finite (R ⧸ P) := Finite.of_injective _ (Ideal.quotientMap_injective (I := RingHom.ker ψ) (f := α))
  haveI hPm : P.IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  have hmm : (RingHom.ker ψ).IsMaximal := Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  letI := Ideal.Quotient.field P
  let Q : Ideal S := P.map (algebraMap R S)
  letI : Algebra (R ⧸ P) K := (RingHom.kerLift (ψ.comp α)).toAlgebra
  haveI : Algebra.FiniteType (R ⧸ P) (S ⧸ Q) := Algebra.FiniteType.of_restrictScalars_finiteType R _ _
  letI : Algebra (R ⧸ P) B := ((algebraMap K B).comp (algebraMap (R ⧸ P) K)).toAlgebra
  haveI : IsScalarTower (R ⧸ P) K B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hβ' : ∀ r, β (α r) = algebraMap K B (ψ (α r)) := fun r => congr($hβ r)
  have hQβ : ∀ a ∈ Q, β a = 0 := by
    intro a ha
    refine (show Q ≤ RingHom.ker β from Ideal.map_le_iff_le_comap.mpr fun r hr => ?_) ha
    have hr' : ψ (α r) = 0 := hr
    change β (α r) = 0
    rw [hβ', hr', map_zero]
  have hQψ : Q ≤ RingHom.ker ψ := Ideal.map_le_iff_le_comap.mpr fun r hr => hr
  let β' : S ⧸ Q →ₐ[R ⧸ P] B :=
    { Ideal.Quotient.lift Q β hQβ with
      commutes' := fun r => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact hβ' r }
  let φ : K ⊗[R ⧸ P] (S ⧸ Q) →ₐ[K] B := Algebra.TensorProduct.lift (Algebra.ofId K B) β' fun _ _ => Commute.all _ _
  have hφ : ∀ a : S, φ (1 ⊗ₜ Ideal.Quotient.mk Q a) = β a := fun a => by
    simp [φ, β']
  have hsurj : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hgen]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨a, rfl⟩
    exact ⟨_, hφ a⟩
  have hker : RingHom.ker φ ≤ nilradical _ := by
    intro a ha
    refine mem_nilradical_of_forall_algHom (K := K) a fun χ' => ?_
    let ψ' : S →+* K := χ'.toRingHom.comp
      ((Algebra.TensorProduct.includeRight (R := R ⧸ P) (A := K) (B := S ⧸ Q)).toRingHom.comp (Ideal.Quotient.mk Q))
    obtain ⟨χ, hχ⟩ := hpt ψ' (by
      ext r
      have : (1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r)) = algebraMap K _ (ψ (α r)) := by
        change (1 : K) ⊗ₜ[R ⧸ P] (algebraMap (R ⧸ P) (S ⧸ Q) (Ideal.Quotient.mk P r)) =
          (algebraMap (R ⧸ P) K (Ideal.Quotient.mk P r)) ⊗ₜ 1
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      change χ' ((1 : K) ⊗ₜ[R ⧸ P] (Ideal.Quotient.mk Q (α r))) = ψ (α r)
      rw [this, AlgHom.commutes]
      rfl)
    have e : χ.comp φ = χ' := by
      ext b
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      change χ (φ (1 ⊗ₜ Ideal.Quotient.mk Q b)) = χ' (1 ⊗ₜ Ideal.Quotient.mk Q b)
      rw [hφ]
      exact congr($hχ b)
    have ha' : φ a = 0 := ha
    rw [← e, AlgHom.comp_apply, ha', map_zero]
  obtain ⟨χ, hχ⟩ := hpt ψ rfl
  have hχ' : ∀ a, χ (β a) = ψ a := fun a => congr($hχ a)
  haveI := AugCot.smooth_of_locally h
  have hmem : ∀ a : S, Ideal.Quotient.mk Q a ∈ (RingHom.ker ψ).map (Ideal.Quotient.mk Q) ↔ a ∈ RingHom.ker ψ :=
    fun a => by
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hQψ]
  obtain ⟨u, s, hs, hu, hus⟩ := GlobalTheory.LocalCoord.exists_local_coordinates (R ⧸ P) (S ⧸ Q) K B φ χ g ((RingHom.ker ψ).map (Ideal.Quotient.mk Q))
    hsurj hker (fun a => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [hmem, hφ, hχ', RingHom.mem_ker])
    ((Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hmm).resolve_left fun ht =>
      hmm.ne_top (Ideal.eq_top_iff_one _ |>.mpr ((hmem 1).mp (ht ▸ trivial))))
    (exists_local_generators h χ) (isReduced_of_smooth_of_isIntegrallyClosed K B)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  choose v hv using fun i => Ideal.Quotient.mk_surjective (u i)
  refine ⟨v, s, fun h => hs ((hmem s).mpr h), fun i => (hmem _).mp (hv i ▸ hu i), fun a ha => ?_⟩
  have h1 := hus _ ((hmem a).mpr ha)
  have h2 : Ideal.span (Set.range u) ⊔ nilradical (S ⧸ Q) =
      (Ideal.span (Set.range v) ⊔ Q.radical).map (Ideal.Quotient.mk Q) := by
    rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp, Ideal.map_radical_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]), Ideal.map_quotient_self]
    congr 3
    exact funext fun i => (hv i).symm
  rw [h2, ← map_mul, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_assoc, sup_eq_left.mpr (Ideal.le_radical (I := Q))] at h1
  exact h1

open TensorProduct in

/- English proof (translation)
Use `letI := α.toAlgebra`. Use `letI := ρ.toAlgebra`. Set `T` to `K ⊗[R] S`. Apply the tactic sequence `let j : Sp T ⟶ pullback f ζ := (pullbackSpecIso R K S).inv ≫ (pullbackSymmetry _ _).hom ≫ pullback.map (spMap α) (spMap ρ) f ζ iW (𝟙 _) iV hsq.symm (by rw [hζ, Category.id_comp])`. Use `haveI : IsOpenImmersion j := by dsimp only [j] infer_instance`.

Set `iL : K →+* T` to `Algebra.TensorProduct.includeLeftRingHom`. Set `iR : S →+* T` to `(Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S) : S →+* T)`. Establish `hj1 : j ≫ pullback.fst f ζ = spMap iR ≫ iW`. Simplify using `only [j, Category.assoc, pullback.lift_fst]`. Rewrite using `[pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]`.

Establish `hj2 : j ≫ pullback.snd f ζ = spMap iL`. Simplify using `only [j, Category.assoc, pullback.lift_snd, Category.comp_id]`. Rewrite using `[pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]`. Take `⟨I, e, he⟩` from `IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion (pullback.snd h j))`. Set `I' : Ideal T` to `I`.

Establish `hmk : e.inv ≫ pullback.snd h j = spMap (Ideal.Quotient.mk I')`. Rewrite using `[he, Iso.inv_hom_id_assoc]`. Use `⟨T ⧸ I', inferInstance, inferInstance, (Ideal.Quotient.mk I').comp iR, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AugCot.locally_iff_smoothOfRelativeDimension]`. Establish `: Spec.map (CommRingCat.ofHom (algebraMap K (T ⧸ I'))) = (e.inv ≫ pullback.fst h j) ≫ h ≫ pullback.snd f ζ`.

Rewrite using `[Category.assoc, pullback.condition_assoc, hj2, ← Category.assoc, hmk, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `smoothOfRelativeDimension_comp 0 g (e.inv ≫ pullback.fst h j) (h ≫ pullback.snd f ζ)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Use extensionality with `r`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk I' (1 ⊗ₜ algebraMap R S r) = Ideal.Quotient.mk I' (algebraMap R K r ⊗ₜ 1)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Rewrite using `[eq_top_iff]`. Introduce and unpack `b -`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `tmul a s`. Establish `: Ideal.Quotient.mk I' (a ⊗ₜ s) = a • Ideal.Quotient.mk I' (1 ⊗ₜ s)`. Rewrite using `[← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]`. Rewrite using `[this]`.

Conclude with `Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self (f := (Ideal.Quotient.mk I').comp iR) s)) _`. Introduce `ψ' hψ'`. Set `ψa : S →ₐ[R] K` to `{ ψ' with commutes' := fun r => congr($hψ' r) }`. Set `θ : T →ₐ[K] K` to `Algebra.TensorProduct.lift (AlgHom.id K K) ψa fun _ _ => Commute.all _ _`. Establish `hθ : spMap (θ : T →+* K) ≫ spMap iL = 𝟙 _`.

Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Use `congr 1`. Use extensionality with `a`. Conclude with `θ.commutes a`. Take `⟨c, hc⟩` from `hpt (spMap (θ : T →+* K) ≫ j) (by rw [Category.assoc, hj2, hθ])`.

Set `χ₀ : T ⧸ I' →+* K` to `(Spec.preimage (pullback.lift c _ hc ≫ e.hom)).hom`. Establish `hχ : χ₀.comp (Ideal.Quotient.mk I') = θ`. Establish `: spMap (χ₀.comp (Ideal.Quotient.mk I')) = spMap (θ : T →+* K)`. Establish `h1 : spMap χ₀ = pullback.lift c _ hc ≫ e.hom` using `Spec.map_preimage _`. Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I') ≫ CommRingCat.ofHom χ₀) = _`.

Rewrite using `[Spec.map_comp]`. Express the relevant statement in the definitionally equal form `spMap χ₀ ≫ spMap (Ideal.Quotient.mk I') = _`. Rewrite using `[h1, ← hmk, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]`. Conclude with `congr($(Spec.map_injective this).hom)`. Use `⟨{ χ₀ with commutes' := fun a => ?_ }, ?_⟩` and prove the remaining obligations.

Conclude with `(congr($hχ (algebraMap K T a)) :).trans (θ.commutes a)`. Use extensionality with `s`. Establish `h3 : θ (1 ⊗ₜ s) = ψ' s`. Simplify using `only [θ, T, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]`. Both sides reduce to the same expression.

Conclude with `(congr($hχ (1 ⊗ₜ s)) :).trans h3`.
-/
theorem exists_chart_ring {G Z H : Scheme.{0}} (f : G ⟶ Z) {R S K : Type} [CommRing R] [CommRing S] [Field K]
    {g : ℕ} (α : R →+* S) (ρ : R →+* K) (iW : Sp S ⟶ G) (iV : Sp R ⟶ Z) [IsOpenImmersion iW] [IsOpenImmersion iV]
    (hsq : iW ≫ f = spMap α ≫ iV) (ζ : Sp K ⟶ Z) (hζ : ζ = spMap ρ ≫ iV) (h : H ⟶ pullback f ζ)
    [IsClosedImmersion h] [SmoothOfRelativeDimension g (h ≫ pullback.snd f ζ)]
    (hpt : ∀ x : Sp K ⟶ pullback f ζ, x ≫ pullback.snd f ζ = 𝟙 _ → ∃ c : Sp K ⟶ H, c ≫ h = x) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra K B) (β : S →+* B),
      RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap K B) ∧
      β.comp α = (algebraMap K B).comp ρ ∧ Algebra.adjoin K (Set.range β) = ⊤ ∧
      ∀ ψ' : S →+* K, ψ'.comp α = ρ → ∃ χ : B →ₐ[K] K, (χ : B →+* K).comp β = ψ' := by
  letI := α.toAlgebra
  letI := ρ.toAlgebra
  let T := K ⊗[R] S
  let j : Sp T ⟶ pullback f ζ := (pullbackSpecIso R K S).inv ≫ (pullbackSymmetry _ _).hom ≫
    pullback.map (spMap α) (spMap ρ) f ζ iW (𝟙 _) iV hsq.symm (by rw [hζ, Category.id_comp])
  haveI : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let iL : K →+* T := Algebra.TensorProduct.includeLeftRingHom
  let iR : S →+* T := (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := S) : S →+* T)
  have hj1 : j ≫ pullback.fst f ζ = spMap iR ≫ iW := by
    simp only [j, Category.assoc, pullback.lift_fst]
    rw [pullbackSymmetry_hom_comp_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  have hj2 : j ≫ pullback.snd f ζ = spMap iL := by
    simp only [j, Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [pullbackSymmetry_hom_comp_snd, pullbackSpecIso_inv_fst]
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp (inferInstance : IsClosedImmersion (pullback.snd h j))
  let I' : Ideal T := I
  have hmk : e.inv ≫ pullback.snd h j = spMap (Ideal.Quotient.mk I') := by
    rw [he, Iso.inv_hom_id_assoc]
  refine ⟨T ⧸ I', inferInstance, inferInstance, (Ideal.Quotient.mk I').comp iR, ?_, ?_, ?_, ?_⟩
  · rw [AugCot.locally_iff_smoothOfRelativeDimension]
    have : Spec.map (CommRingCat.ofHom (algebraMap K (T ⧸ I'))) =
        (e.inv ≫ pullback.fst h j) ≫ h ≫ pullback.snd f ζ := by
      rw [Category.assoc, pullback.condition_assoc, hj2, ← Category.assoc, hmk, ← Spec.map_comp]
      rfl
    rw [this]
    have := smoothOfRelativeDimension_comp 0 g (e.inv ≫ pullback.fst h j) (h ≫ pullback.snd f ζ)
    rwa [zero_add] at this
  · ext r
    change Ideal.Quotient.mk I' (1 ⊗ₜ algebraMap R S r) = Ideal.Quotient.mk I' (algebraMap R K r ⊗ₜ 1)
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  · rw [eq_top_iff]
    rintro b -
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    induction b using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
    | tmul a s =>
      have : Ideal.Quotient.mk I' (a ⊗ₜ s) = a • Ideal.Quotient.mk I' (1 ⊗ₜ s) := by
        rw [← Ideal.Quotient.mkₐ_eq_mk K, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this]
      exact Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self (f := (Ideal.Quotient.mk I').comp iR) s)) _
  · intro ψ' hψ'
    let ψa : S →ₐ[R] K := { ψ' with commutes' := fun r => congr($hψ' r) }
    let θ : T →ₐ[K] K := Algebra.TensorProduct.lift (AlgHom.id K K) ψa fun _ _ => Commute.all _ _
    have hθ : spMap (θ : T →+* K) ≫ spMap iL = 𝟙 _ := by
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      ext a
      exact θ.commutes a
    obtain ⟨c, hc⟩ := hpt (spMap (θ : T →+* K) ≫ j) (by rw [Category.assoc, hj2, hθ])
    let χ₀ : T ⧸ I' →+* K := (Spec.preimage (pullback.lift c _ hc ≫ e.hom)).hom
    have hχ : χ₀.comp (Ideal.Quotient.mk I') = θ := by
      have : spMap (χ₀.comp (Ideal.Quotient.mk I')) = spMap (θ : T →+* K) := by
        have h1 : spMap χ₀ = pullback.lift c _ hc ≫ e.hom := Spec.map_preimage _
        change Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I') ≫ CommRingCat.ofHom χ₀) = _
        rw [Spec.map_comp]
        change spMap χ₀ ≫ spMap (Ideal.Quotient.mk I') = _
        rw [h1, ← hmk, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd]
      exact congr($(Spec.map_injective this).hom)
    refine ⟨{ χ₀ with commutes' := fun a => ?_ }, ?_⟩
    · exact (congr($hχ (algebraMap K T a)) :).trans (θ.commutes a)
    · ext s
      have h3 : θ (1 ⊗ₜ s) = ψ' s := by
        simp only [θ, T, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
        rfl
      exact (congr($hχ (1 ⊗ₜ s)) :).trans h3

/- English proof (translation)
Substitute `hm` using the available equality. Use `letI := G.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)`. Use `haveI := hW.isLocalization_stalk ⟨w, hw⟩`. Establish `hmem : ∀ a : Γ(G, W), (G.presheaf.germ W w hw).hom a ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk w) ↔ a ∈ (hW.primeIdealOf ⟨w, hw⟩).asIdeal` using `fun a => IsLocalization.AtPrime.to_map_mem_maximal_iff (G.presheaf.stalk w) (hW.primeIdealOf ⟨w, hw⟩).asIdeal a`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (hW.primeIdealOf ⟨w, hw⟩).asIdeal (G.presheaf.stalk w), Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Establish `h1` using `Ideal.mem_map_of_mem (G.presheaf.germ W w hw).hom (H a ha)`. Establish `hsu : IsUnit ((G.presheaf.germ W w hw).hom s)`. Assume the negation of the conclusion as `hn`.

Conclude with `hs ((hmem s).mp hn)`. Rewrite `h1` using `[map_mul, Ideal.unit_mul_mem_iff_mem _ hsu, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]`. Use `SetLike.le_def.mp (sup_le_sup_left (le_trans (Ideal.map_radical_le _) (Ideal.radical_mono ?_)) _) h1` and prove the remaining obligations. Rewrite using `[Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `r hr`.

Establish `e : (G.presheaf.germ W w hw).hom ((f.appLE V W hle).hom r) = (f.stalkMap w).hom ((Z.presheaf.germ V (f w) (hle hw)).hom r)`. Establish `e' : f.appLE V W hle ≫ G.presheaf.germ W w hw = Z.presheaf.germ V (f w) (hle hw) ≫ f.stalkMap w`. Use `Eq.trans ?_ (Scheme.Hom.germ_stalkMap f V w (hle hw)).symm` and prove the remaining obligations. Rewrite using `[Scheme.Hom.appLE, Category.assoc, G.presheaf.germ_res]`. Conclude with `congr($(e').hom r)`.

Establish `h2` using `(hmem _).mpr hr`. Rewrite using `[Ideal.mem_comap, RingHom.comp_apply]`. Rewrite `h2`, the goal using `[e]`. Conclude with `Ideal.mem_map_of_mem _ fun hn => h2 (hn.map _)`. Use `sup_le (Ideal.span_le.mpr ?_) ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(hmem _).mpr (hu i)`. Rewrite using `[Ideal.IsPrime.radical_le_iff inferInstance]`. Conclude with `IsLocalRing.map_maximalIdeal_le _`.
-/
theorem maximalIdeal_stalk_eq {G Z : Scheme.{0}} (f : G ⟶ Z) {V : Z.Opens} {W : G.Opens} (hW : IsAffineOpen W)
    (hle : W ≤ f ⁻¹ᵁ V) (w : G) (hw : w ∈ W) {g : ℕ} (u : Fin g → Γ(G, W)) (s : Γ(G, W)) (m : Ideal Γ(G, W))
    (hm : m = (hW.primeIdealOf ⟨w, hw⟩).asIdeal) (hs : s ∉ m) (hu : ∀ i, u i ∈ m)
    (H : ∀ a ∈ m, s * a ∈ Ideal.span (Set.range u) ⊔
      ((m.comap (f.appLE V W hle).hom).map (f.appLE V W hle).hom).radical) :
    IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
        ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (f w))).map (f.stalkMap w).hom).radical := by
  subst hm
  letI := G.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)
  haveI := hW.isLocalization_stalk ⟨w, hw⟩
  have hmem : ∀ a : Γ(G, W), (G.presheaf.germ W w hw).hom a ∈ IsLocalRing.maximalIdeal (G.presheaf.stalk w) ↔
      a ∈ (hW.primeIdealOf ⟨w, hw⟩).asIdeal := fun a =>
    IsLocalization.AtPrime.to_map_mem_maximal_iff (G.presheaf.stalk w) (hW.primeIdealOf ⟨w, hw⟩).asIdeal a
  apply le_antisymm
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hW.primeIdealOf ⟨w, hw⟩).asIdeal (G.presheaf.stalk w),
      Ideal.map_le_iff_le_comap]
    intro a ha
    have h1 := Ideal.mem_map_of_mem (G.presheaf.germ W w hw).hom (H a ha)
    have hsu : IsUnit ((G.presheaf.germ W w hw).hom s) := by
      by_contra hn
      exact hs ((hmem s).mp hn)
    rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hsu, Ideal.map_sup, Ideal.map_span, ← Set.range_comp] at h1
    refine SetLike.le_def.mp (sup_le_sup_left (le_trans (Ideal.map_radical_le _) (Ideal.radical_mono ?_)) _) h1
    rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro r hr
    have e : (G.presheaf.germ W w hw).hom ((f.appLE V W hle).hom r) =
        (f.stalkMap w).hom ((Z.presheaf.germ V (f w) (hle hw)).hom r) := by
      have e' : f.appLE V W hle ≫ G.presheaf.germ W w hw = Z.presheaf.germ V (f w) (hle hw) ≫ f.stalkMap w := by
        refine Eq.trans ?_ (Scheme.Hom.germ_stalkMap f V w (hle hw)).symm
        rw [Scheme.Hom.appLE, Category.assoc, G.presheaf.germ_res]
      exact congr($(e').hom r)
    have h2 := (hmem _).mpr hr
    rw [Ideal.mem_comap, RingHom.comp_apply]
    rw [e] at h2 ⊢
    exact Ideal.mem_map_of_mem _ fun hn => h2 (hn.map _)
  · refine sup_le (Ideal.span_le.mpr ?_) ?_
    · rintro _ ⟨i, rfl⟩
      exact (hmem _).mpr (hu i)
    · rw [Ideal.IsPrime.radical_le_iff inferInstance]
      exact IsLocalRing.map_maximalIdeal_le _

end FibreCoord
open FibreCoord

/- English proof (translation)
Introduce `C hT hF w hwc`. Take `⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, -⟩` from `GlobalTheory.ZJ.core_basic C`. Use `haveI := C.lft`. Take `⟨p, _, b, hb, hbU⟩` from `padicAlgCl_integral_points.1 C.G.toScheme (C.GG.hom ≫ C.π) w hwc (C.GG.hom ⁻¹ᵁ C.U) (by`. Take `⟨z, hz, x, rfl⟩` from `C.GG.hom.denseRange.inter_open_nonempty _ C.U.isOpen C.ne`.

Conclude with `⟨x, hz⟩)`. Use `haveI := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1`. Take `⟨τ⟩` from `hT p (b ≫ C.GG.hom) (by`. Introduce and unpack `_ ⟨t, rfl⟩`. Use `hbU ⟨t, rfl⟩` as an intermediate fact.

Rewrite using `[← Category.assoc, Scheme.Hom.comp_apply]`. Conclude with `this)`. Take `⟨V, hV, hzV, -⟩` from `exists_isAffineOpen_mem_and_subset (X := C.Z) (x := C.GG.hom w) (U := ⊤) trivial`. Take `⟨W, hW, hw, hle⟩` from `exists_isAffineOpen_mem_and_subset (X := C.G.toScheme) (x := w) (U := C.GG.hom ⁻¹ᵁ V) hzV`. Establish `hle' : W ≤ C.GG.hom ⁻¹ᵁ V` using `hle`.

Establish `hxw : ∀ t, (rPt p ≫ b) t = w` using `fun t => by`. Rewrite using `[Scheme.Hom.comp_apply, ← hb]`. Use `congr 1`. Rewrite using `[Subsingleton.elim t (IsLocalRing.closedPoint (kb p))]`. Conclude with `IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))`.

Establish `hr : Set.range (rPt p ≫ b) ⊆ Set.range hW.fromSpec`. Rewrite using `[hW.range_fromSpec]`. Introduce and unpack `_ ⟨t, rfl⟩`. Rewrite using `[hxw]`. Conclude with `hw`.

Set `ψ : Γ(C.G.toScheme, W) →+* kb p` to `(Spec.preimage (IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr)).hom`. Establish `hψ : spMap ψ ≫ hW.fromSpec = rPt p ≫ b`. Establish `h1 : spMap ψ = IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr` using `Spec.map_preimage _`. Rewrite using `[h1, IsOpenImmersion.lift_fac]`. Establish `hm : RingHom.ker ψ = (hW.primeIdealOf ⟨w, hw⟩).asIdeal`.

Establish `h1 : spMap ψ (IsLocalRing.closedPoint (kb p)) = hW.primeIdealOf ⟨w, hw⟩`. Apply `hW.fromSpec.isOpenEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hW.fromSpec_primeIdealOf]`. Use `(Scheme.Hom.comp_apply _ _ _).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hψ]`.

Conclude with `hxw _`. Rewrite using `[← h1, RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot]`. Both sides reduce to the same expression. Set `α : Γ(C.Z, V) →+* Γ(C.G.toScheme, W)` to `(C.GG.hom.appLE V W hle').hom`. Establish `hsq : hW.fromSpec ≫ C.GG.hom = spMap α ≫ hV.fromSpec` using `(IsAffineOpen.SpecMap_appLE_fromSpec C.GG.hom hV hW hle').symm`.

Set `h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (rPt p ≫ b ≫ C.GG.hom)` to `pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by`. Rewrite using `[Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac])`. Establish `h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f` using `pullback.lift_fst _ _ _`. Establish `h2 : h ≫ pullback.snd _ _ = pullback.snd _ _` using `pullback.lift_snd _ _ _`. Use `haveI := τ.imm h h1 h2`.

Use `haveI : SmoothOfRelativeDimension C.g (h ≫ pullback.snd _ _) := by`. Rewrite using `[h2]`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange (n := C.g)).of_isPullback (IsPullback.of_hasPullback _ _) τ.smooth`. Take `⟨B, _, _, β, hB, hβ, hgen, hpt⟩` from `exists_chart_ring (g := C.g) C.GG.hom α (ψ.comp α) hW.fromSpec hV.fromSpec hsq (rPt p ≫ b ≫ C.GG.hom) (by`. Rewrite using `[← Category.assoc, ← hψ, Category.assoc, hsq, ← Category.assoc, ← Spec.map_comp]`.

Use the proof step `rfl) h (fun x hx => by`. Take `⟨c, hc, hc'⟩` from `hF p _ τ (x ≫ pullback.fst _ _) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])`. Use `⟨pullback.lift c (𝟙 _) (by rw [hc, Category.id_comp]), ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, h1, pullback.lift_fst_assoc, hc']`. Rewrite using `[Category.assoc, h2, pullback.lift_snd, hx])`. Use `haveI : Finite (Γ(C.G.toScheme, W) ⧸ RingHom.ker ψ) := by haveI := (jacobson_closedPoints_tools_int _ (C.GG.hom ≫ C.π)).2.1 w hwc`. Use `letI := C.G.toScheme.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)`. Use `haveI := hW.isLocalization_stalk ⟨w, hw⟩`.

Use `haveI : Finite (C.G.toScheme.presheaf.stalk w ⧸ IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w)) := ‹Finite (C.G.toScheme.residueField w)›`. Rewrite using `[hm, ← IsLocalization.AtPrime.comap_maximalIdeal (C.G.toScheme.presheaf.stalk w) (hW.primeIdealOf ⟨w, hw⟩).asIdeal]`. Conclude with `Finite.of_injective _ Ideal.quotientMap_injective`. Take `⟨u, s, hs, hu, H⟩` from `exists_coords_ring α (HasRingHomProperty.appLE @LocallyOfFiniteType C.GG.hom hlft ⟨V, hV⟩ ⟨W, hW⟩ hle') ψ hB β hβ hgen hpt`. Conclude with `⟨W, hw, u, hW, maximalIdeal_stalk_eq C.GG.hom hW hle' w hw u s _ hm hs hu H⟩`.
-/
theorem Core.exists_coord : ∀ C : Core, C.HasTests → C.Fib → ∀ w : C.G.toScheme, IsClosed ({w} : Set C.G.toScheme) → ∃ (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsAffineOpen W ∧ C.Coord w W hw u := by
  intro C hT hF w hwc
  obtain ⟨-, hlft, -, hint, hflat, -, -, -, -, -, -, hdom, -⟩ := GlobalTheory.ZJ.core_basic C
  haveI := C.lft
  obtain ⟨p, _, b, hb, hbU⟩ := padicAlgCl_integral_points.1 C.G.toScheme (C.GG.hom ≫ C.π) w hwc
    (C.GG.hom ⁻¹ᵁ C.U) (by
      obtain ⟨z, hz, x, rfl⟩ := C.GG.hom.denseRange.inter_open_nonempty _ C.U.isOpen C.ne
      exact ⟨x, hz⟩)
  haveI := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  obtain ⟨τ⟩ := hT p (b ≫ C.GG.hom) (by
    rintro _ ⟨t, rfl⟩
    have := hbU ⟨t, rfl⟩
    rw [← Category.assoc, Scheme.Hom.comp_apply]
    exact this)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (X := C.Z) (x := C.GG.hom w) (U := ⊤) trivial
  obtain ⟨W, hW, hw, hle⟩ := exists_isAffineOpen_mem_and_subset (X := C.G.toScheme) (x := w)
    (U := C.GG.hom ⁻¹ᵁ V) hzV
  have hle' : W ≤ C.GG.hom ⁻¹ᵁ V := hle
  have hxw : ∀ t, (rPt p ≫ b) t = w := fun t => by
    rw [Scheme.Hom.comp_apply, ← hb]
    congr 1
    rw [Subsingleton.elim t (IsLocalRing.closedPoint (kb p))]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue (OO p))
  have hr : Set.range (rPt p ≫ b) ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨t, rfl⟩
    rw [hxw]
    exact hw
  let ψ : Γ(C.G.toScheme, W) →+* kb p := (Spec.preimage (IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr)).hom
  have hψ : spMap ψ ≫ hW.fromSpec = rPt p ≫ b := by
    have h1 : spMap ψ = IsOpenImmersion.lift hW.fromSpec (rPt p ≫ b) hr := Spec.map_preimage _
    rw [h1, IsOpenImmersion.lift_fac]
  have hm : RingHom.ker ψ = (hW.primeIdealOf ⟨w, hw⟩).asIdeal := by
    have h1 : spMap ψ (IsLocalRing.closedPoint (kb p)) = hW.primeIdealOf ⟨w, hw⟩ := by
      apply hW.fromSpec.isOpenEmbedding.injective
      rw [hW.fromSpec_primeIdealOf]
      refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
      rw [hψ]
      exact hxw _
    rw [← h1, RingHom.ker_eq_comap_bot, ← IsLocalRing.maximalIdeal_eq_bot]
    rfl
  let α : Γ(C.Z, V) →+* Γ(C.G.toScheme, W) := (C.GG.hom.appLE V W hle').hom
  have hsq : hW.fromSpec ≫ C.GG.hom = spMap α ≫ hV.fromSpec :=
    (IsAffineOpen.SpecMap_appLE_fromSpec C.GG.hom hV hW hle').symm
  let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (rPt p ≫ b ≫ C.GG.hom) :=
    pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
      rw [Category.assoc, τ.f_over, pullback.condition_assoc, Category.assoc, τ.fac])
  have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
  have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  haveI := τ.imm h h1 h2
  haveI : SmoothOfRelativeDimension C.g (h ≫ pullback.snd _ _) := by
    rw [h2]
    exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := C.g)).of_isPullback
      (IsPullback.of_hasPullback _ _) τ.smooth
  obtain ⟨B, _, _, β, hB, hβ, hgen, hpt⟩ := exists_chart_ring (g := C.g) C.GG.hom α (ψ.comp α) hW.fromSpec
    hV.fromSpec hsq (rPt p ≫ b ≫ C.GG.hom) (by
      rw [← Category.assoc, ← hψ, Category.assoc, hsq, ← Category.assoc, ← Spec.map_comp]
      rfl) h (fun x hx => by
      obtain ⟨c, hc, hc'⟩ := hF p _ τ (x ≫ pullback.fst _ _) (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hx, Category.id_comp])
      refine ⟨pullback.lift c (𝟙 _) (by rw [hc, Category.id_comp]), ?_⟩
      apply pullback.hom_ext
      · rw [Category.assoc, h1, pullback.lift_fst_assoc, hc']
      · rw [Category.assoc, h2, pullback.lift_snd, hx])
  haveI : Finite (Γ(C.G.toScheme, W) ⧸ RingHom.ker ψ) := by
    haveI := (jacobson_closedPoints_tools_int _ (C.GG.hom ≫ C.π)).2.1 w hwc
    letI := C.G.toScheme.presheaf.algebra_section_stalk (⟨w, hw⟩ : W)
    haveI := hW.isLocalization_stalk ⟨w, hw⟩
    haveI : Finite (C.G.toScheme.presheaf.stalk w ⧸ IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w)) :=
      ‹Finite (C.G.toScheme.residueField w)›
    rw [hm, ← IsLocalization.AtPrime.comap_maximalIdeal (C.G.toScheme.presheaf.stalk w)
      (hW.primeIdealOf ⟨w, hw⟩).asIdeal]
    exact Finite.of_injective _ Ideal.quotientMap_injective
  obtain ⟨u, s, hs, hu, H⟩ := exists_coords_ring α
    (HasRingHomProperty.appLE @LocallyOfFiniteType C.GG.hom hlft ⟨V, hV⟩ ⟨W, hW⟩ hle') ψ hB β hβ hgen hpt
  exact ⟨W, hw, u, hW, maximalIdeal_stalk_eq C.GG.hom hW hle' w hw u s _ hm hs hu H⟩

end GlobalTheory.ZJ
