import Mathlib
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.GenIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullDimQuotientMinimalPrimeOverL
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad

namespace ChowFormHeightComparison₂.CF

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/- English proof (translation)
Establish `: FaithfulSMul ℤ (A ⧸ q)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hinj`. Establish `: Algebra.FiniteType ℤ (A ⧸ q)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)`. Take `⟨e, he⟩` from `exists_trdeg_eq_natCast ℤ (A := A ⧸ q)`. Establish `h1` using `GroundTheory.Heights₂.Heights.IntDomainDim.proof (A ⧸ q) hinj`. Rewrite `h1` using `[he, Cardinal.toENat_nat]`.

Establish `hB` using `ringKrullDim_genericFibre_eq ℤ ℚ hd`. Establish `hB'` using `ringKrullDim_genericFibre_eq ℤ ℚ he`. Use `IsLocalization.tensorRight (S := A) ℚ (nonZeroDivisors ℤ)` as an intermediate fact. Use `IsLocalization.tensorRight (S := A ⧸ q) ℚ (nonZeroDivisors ℤ)` as an intermediate fact. Establish `hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) ≤ nonZeroDivisors A` using `Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero (by simpa using nonZeroDivisors.ne_zero hx)`.

Establish `hle' : Algebra.algebraMapSubmonoid (A ⧸ q) (nonZeroDivisors ℤ) ≤ nonZeroDivisors (A ⧸ q)` using `Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hx))`. Establish `: IsDomain (ℚ ⊗[ℤ] A)` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ hle`. Establish `: IsDomain (ℚ ⊗[ℤ] (A ⧸ q))` using `IsLocalization.isDomain_of_le_nonZeroDivisors _ hle'`. Set `φ : ℚ ⊗[ℤ] A →ₐ[ℚ] ℚ ⊗[ℤ] (A ⧸ q)` to `Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Ideal.Quotient.mkₐ ℤ q)`. Establish `hφ : Function.Surjective φ` using `fun x => by`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `tmul a b`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Conclude with `⟨a ⊗ₜ b, rfl⟩`.

Consider the case `add x y hx hy`. Take `⟨x, rfl⟩` from `hx`. Take `⟨y, rfl⟩` from `hy`. Conclude with `⟨x + y, map_add _ _ _⟩`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime _`.

Establish `hc : (RingHom.ker φ).comap (algebraMap A (ℚ ⊗[ℤ] A)) = q`. Use extensionality with `a`. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff _ (IsLocalization.injective (ℚ ⊗[ℤ] (A ⧸ q)) hle')]`. Conclude with `Iff.rfl`. Establish `h2` using `IsLocalization.height_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ)) (RingHom.ker φ)`.

Use `replace h2 : q.height = (RingHom.ker φ).height := (congrArg Ideal.height hc).symm.trans h2`. Establish `h3` using `height_add_ringKrullDim_quotient_of_finiteType ℚ (RingHom.ker φ)`. Establish `h4 : ringKrullDim ((ℚ ⊗[ℤ] A) ⧸ RingHom.ker φ) = ringKrullDim (ℚ ⊗[ℤ] (A ⧸ q))` using `ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ)`. Rewrite `h3` using `[h4, hB, hB', ← h2]`. Rewrite using `[h1, ← h3, add_comm, WithBot.coe_add]`.

Use `add_le_add (le_of_eq (by norm_cast)) ?_` and prove the remaining obligations. Conclude with `hq` after adjusting the coercions.
-/
theorem le_dim_quotient_horizontal (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hq : q.height ≤ 1) (hinj : Function.Injective (algebraMap ℤ (A ⧸ q))) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : FaithfulSMul ℤ (A ⧸ q) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  have : Algebra.FiniteType ℤ (A ⧸ q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q) (Ideal.Quotient.mkₐ_surjective ℤ q)
  obtain ⟨e, he⟩ := exists_trdeg_eq_natCast ℤ (A := A ⧸ q)
  have h1 := GroundTheory.Heights₂.Heights.IntDomainDim.proof (A ⧸ q) hinj
  rw [he, Cardinal.toENat_nat] at h1
  have hB := ringKrullDim_genericFibre_eq ℤ ℚ hd
  have hB' := ringKrullDim_genericFibre_eq ℤ ℚ he
  have := IsLocalization.tensorRight (S := A) ℚ (nonZeroDivisors ℤ)
  have := IsLocalization.tensorRight (S := A ⧸ q) ℚ (nonZeroDivisors ℤ)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have hle' : Algebra.algebraMapSubmonoid (A ⧸ q) (nonZeroDivisors ℤ) ≤ nonZeroDivisors (A ⧸ q) :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hx))
  have : IsDomain (ℚ ⊗[ℤ] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  have : IsDomain (ℚ ⊗[ℤ] (A ⧸ q)) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle'
  let φ : ℚ ⊗[ℤ] A →ₐ[ℚ] ℚ ⊗[ℤ] (A ⧸ q) := Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (Ideal.Quotient.mkₐ ℤ q)
  have hφ : Function.Surjective φ := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul a b =>
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨a ⊗ₜ b, rfl⟩
    | add x y hx hy =>
      obtain ⟨x, rfl⟩ := hx
      obtain ⟨y, rfl⟩ := hy
      exact ⟨x + y, map_add _ _ _⟩
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  have hc : (RingHom.ker φ).comap (algebraMap A (ℚ ⊗[ℤ] A)) = q := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, ← Ideal.Quotient.eq_zero_iff_mem,
      ← map_eq_zero_iff _ (IsLocalization.injective (ℚ ⊗[ℤ] (A ⧸ q)) hle')]
    exact Iff.rfl
  have h2 := IsLocalization.height_comap (Algebra.algebraMapSubmonoid A (nonZeroDivisors ℤ)) (RingHom.ker φ)
  replace h2 : q.height = (RingHom.ker φ).height := (congrArg Ideal.height hc).symm.trans h2
  have h3 := height_add_ringKrullDim_quotient_of_finiteType ℚ (RingHom.ker φ)
  have h4 : ringKrullDim ((ℚ ⊗[ℤ] A) ⧸ RingHom.ker φ) = ringKrullDim (ℚ ⊗[ℤ] (A ⧸ q)) :=
    ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective (f := φ.toRingHom) hφ)
  rw [h4, hB, hB', ← h2] at h3
  rw [h1, ← h3, add_comm, WithBot.coe_add]
  refine add_le_add (le_of_eq (by norm_cast)) ?_
  exact_mod_cast hq

/- English proof (translation)
Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing ℤ A`. Take `⟨l, hl⟩` from `CharP.exists (A ⧸ q)`. Break down `CharP.char_is_prime_or_zero (A ⧸ q) l with h | rfl` into its components or cases. Establish `: Fact l.Prime` using `⟨h⟩`. Establish `hlq : (l : A) ∈ q`.

Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `CharP.cast_eq_zero _ l`. Conclude with `(GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q (hmin _ hlq (Nat.cast_ne_zero.2 h.ne_zero)) d hd).ge`. Establish `: CharZero (A ⧸ q)` using `CharP.charP_to_charZero _`. Use `le_dim_quotient_horizontal A q ?_ (algebraMap ℤ (A ⧸ q)).injective_int hd` and prove the remaining obligations.

Distinguish the cases in `h0 : q = ⊥`. Substitute `h0` using the available equality. Rewrite using `[Ideal.height_bot]`. Conclude with `zero_le_one`. Take `⟨f, hf, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h0`.

Conclude with `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ (hmin f hf hf0)`.
-/
theorem le_dim_quotient (A : Type) [CommRing A] [IsDomain A] [CharZero A] [Algebra.FiniteType ℤ A]
    (q : Ideal A) [q.IsPrime] (hmin : ∀ f ∈ q, f ≠ 0 → q ∈ (Ideal.span {f}).minimalPrimes) {d : ℕ}
    (hd : Algebra.trdeg ℤ A = d) : (d : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨l, hl⟩ := CharP.exists (A ⧸ q)
  rcases CharP.char_is_prime_or_zero (A ⧸ q) l with h | rfl
  · have : Fact l.Prime := ⟨h⟩
    have hlq : (l : A) ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact CharP.cast_eq_zero _ l
    exact (GlobalTheory.ringKrullDim_quotient_eq_trdeg_of_mem_minimalPrimes_natPrime A l q
      (hmin _ hlq (Nat.cast_ne_zero.2 h.ne_zero)) d hd).ge
  · have : CharZero (A ⧸ q) := CharP.charP_to_charZero _
    refine le_dim_quotient_horizontal A q ?_ (algebraMap ℤ (A ⧸ q)).injective_int hd
    by_cases h0 : q = ⊥
    · subst h0
      rw [Ideal.height_bot]
      exact zero_le_one
    · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ (hmin f hf hf0)

/- English proof (translation)
Introduce `k _ X p D hX Z i _ _ hcoh`. Use `hX.isIntegral` as an intermediate fact. Generalize the expression as in `hiz : i (genericPoint Z) = z at hcoh`. Set `t : X ⟶ Sp ℤ` to `p ≫ spMap (Int.castRingHom k)`. Establish `hrange : Set.range i = closure {z}`.

Establish `h₁` using `(genericPoint_spec Z).image i.continuous`. Rewrite `h₁` using `[Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hiz]`. Conclude with `h₁.def.symm`. Rewrite using `[← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]`. Establish `hgen : genericPoint X ∉ closure ({z} : Set X)`.

Introduce `h`. Establish `e : z = genericPoint X` using `((genericPoint_specializes z).antisymm (specializes_iff_mem_closure.2 h)).eq.symm`. Rewrite `hcoh` using `[e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)]`. Conclude with `zero_ne_one hcoh`. Establish `hX1 : topologicalKrullDim (Set.univ : Set X) = (D + 1 : ℕ)` using `(topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX.dim_eq`.

Establish `hup : topologicalKrullDim (closure ({z} : Set X)) + 1 ≤ (D + 1 : ℕ)` using `hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ fun x hx => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩`. Take `⟨N, jN, _, hjN⟩` from `hX.isProjOver`. Use `isProper_str k N` as an intermediate fact. Establish `: IsProper p` using `hjN ▸ inferInstance`. Establish `: IsFinite (spMap (Int.castRingHom k))` using `(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)`.

Establish `: LocallyOfFiniteType t` using `inferInstance`. Establish `: Flat t` using `hX.flat`. Take `⟨A, _, _, instA, _, _, j, _, ⟨a, ha⟩, hjt, hA⟩` from `exists_affine_chart_trdeg_eq t z`. Take `rfl : instA = Ring.toIntAlgebra A` from `Subsingleton.elim _ _`. Establish `: CharZero A` using `⟨fun m n h => Nat.cast_injective (R := ℤ) (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h))⟩`.

Take `⟨d, hd⟩` from `exists_trdeg_eq_natCast ℤ (A := A)`. Establish `hdimX : topologicalKrullDim X ≤ (d + 1 : ℕ)`. Use `topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_` and prove the remaining obligations. Take `⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩` from `exists_affine_chart_trdeg_eq t x`. Use `⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]`. Use `(PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_` and prove the remaining obligations. Establish `hdB : Algebra.trdeg ℤ B = d` using `hB.trans (hA.symm.trans hd)`. Establish `hZ1 : ringKrullDim ℤ ≤ 1`. Conclude with `Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)` after adjusting the coercions.

Use `(IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_` and prove the remaining obligations. Rewrite using `[ringKrullDim_genericFibre_eq ℤ ℚ hdB]`. Use `(add_le_add hZ1 (le_refl ((d : ℕ) : WithBot ℕ∞))).trans_eq ?_` and prove the remaining obligations. Use `push_cast`. Conclude with `add_comm _ _`.

Establish `hDd : D ≤ d`. Use `hX.dim_eq.symm.trans_le hdimX` as an intermediate fact. Establish `: ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞)` using `this`. Conclude with `Nat.le_of_succ_le_succ (by exact_mod_cast this)`. Establish `: a.asIdeal.IsPrime` using `a.isPrime`.

Establish `hmin : ∀ f ∈ a.asIdeal, f ≠ 0 → a.asIdeal ∈ (Ideal.span {f}).minimalPrimes` using `fun f hf hf0 => by`. Use `⟨⟨a.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hf⟩, fun q' hq' hle => ?_⟩` and prove the remaining obligations. Take `⟨hq'p, hlq'⟩` from `hq'`. Assume the negation of the conclusion as `hne`. Establish `hbot : (⊥ : Ideal A) ≠ q'`.

Introduce `h0`. Establish `h1 : f ∈ q'` using `(Ideal.span_singleton_le_iff_mem _).1 hlq'`. Rewrite `h1` using `[← h0, Ideal.mem_bot]`. Conclude with `hf0 h1`. Set `b' : PrimeSpectrum A` to `⟨q', hq'p⟩`.

Set `g : PrimeSpectrum A` to `⟨⊥, Ideal.isPrime_bot⟩`. Establish `hsp (u v : PrimeSpectrum A) : j u ⤳ j v ↔ u.asIdeal ≤ v.asIdeal` using `j.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes u v).symm`. Establish `h₁ : z < j b'`. Rewrite using `[← ha]`. Conclude with `⟨(hsp b' a).2 hle, fun h => hne ((hsp a b').1 h)⟩`.

Establish `h₂ : j b' < j g` using `⟨(hsp g b').2 bot_le, fun h => hbot (le_bot_iff.1 ((hsp b' g).1 h)).symm⟩`. Establish `h₃` using `Order.coheight_add_one_le h₁`. Establish `h₄` using `Order.coheight_add_one_le h₂`. Rewrite `h₃` using `[hcoh]`. Establish `h₅ : (1 : ℕ∞) + 1 ≤ 1` using `(add_le_add_left (le_add_self.trans h₄) 1).trans h₃`.

Conclude with `absurd h₅ (by decide)`. Establish `hq` using `le_dim_quotient A a.asIdeal hmin hd`. Establish `hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤ topologicalKrullDim (closure ({z} : Set X))`. Rewrite using `[ha]`. Conclude with `(Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le`.

Rewrite `hlow` using `[topologicalKrullDim_range_inter_closure_eq j a]`. Use `replace hlow := hq.trans hlow`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=`. Establish `⟨e, he⟩` using `hX.exists_dim_eq i`. Use the proof step `⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩`.

Rewrite `hlow`, `hup`, the goal using `[he]`. Establish `h1 : d ≤ e` using `by exact_mod_cast hlow`. Establish `h2 : e + 1 ≤ D + 1` using `by exact_mod_cast hup`. Establish `: e = D` using `by omega`. Rewrite using `[this]`.
-/
theorem stDim : StDim := by
  intro k _ X p D hX Z i _ _ hcoh
  have := hX.isIntegral
  generalize hiz : i (genericPoint Z) = z at hcoh
  let t : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k)
  have hrange : Set.range i = closure {z} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hiz] at h₁
    exact h₁.def.symm
  rw [← topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange]
  have hgen : genericPoint X ∉ closure ({z} : Set X) := by
    intro h
    have e : z = genericPoint X :=
      ((genericPoint_specializes z).antisymm (specializes_iff_mem_closure.2 h)).eq.symm
    rw [e, Order.coheight_eq_zero.2 (fun y _ => genericPoint_specializes y)] at hcoh
    exact zero_ne_one hcoh
  have hX1 : topologicalKrullDim (Set.univ : Set X) = (D + 1 : ℕ) :=
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans hX.dim_eq
  have hup : topologicalKrullDim (closure ({z} : Set X)) + 1 ≤ (D + 1 : ℕ) :=
    hX1 ▸ topologicalKrullDim_add_one_le isClosed_closure isClosed_univ
      fun x hx => ⟨genericPoint X, trivial, hgen, genericPoint_specializes x⟩
  obtain ⟨N, jN, _, hjN⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hjN ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  have : LocallyOfFiniteType t := inferInstance
  have : Flat t := hX.flat
  obtain ⟨A, _, _, instA, _, _, j, _, ⟨a, ha⟩, hjt, hA⟩ := exists_affine_chart_trdeg_eq t z
  obtain rfl : instA = Ring.toIntAlgebra A := Subsingleton.elim _ _
  have : CharZero A := ⟨fun m n h => Nat.cast_injective (R := ℤ) (FaithfulSMul.algebraMap_injective ℤ A (by simpa using h))⟩
  obtain ⟨d, hd⟩ := exists_trdeg_eq_natCast ℤ (A := A)
  have hdimX : topologicalKrullDim X ≤ (d + 1 : ℕ) := by
    refine topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨B, _, _, _, _, _, j', _, ⟨b, rfl⟩, -, hB⟩ := exists_affine_chart_trdeg_eq t x
    refine ⟨Set.range j', j'.isOpenEmbedding.isOpen_range, ⟨b, rfl⟩, ?_⟩
    rw [topologicalKrullDim_eq_of_isEmbedding j'.isOpenEmbedding.isEmbedding rfl]
    refine (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim B).le.trans ?_
    have hdB : Algebra.trdeg ℤ B = d := hB.trans (hA.symm.trans hd)
    have hZ1 : ringKrullDim ℤ ≤ 1 := by
      exact_mod_cast Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 ℤ)
    refine (IntModel.ringKrullDim_le_add (O := ℤ) ℚ).trans ?_
    rw [ringKrullDim_genericFibre_eq ℤ ℚ hdB]
    refine (add_le_add hZ1 (le_refl ((d : ℕ) : WithBot ℕ∞))).trans_eq ?_
    push_cast
    exact add_comm _ _
  have hDd : D ≤ d := by
    have := hX.dim_eq.symm.trans_le hdimX
    have : ((D + 1 : ℕ) : WithBot ℕ∞) ≤ ((d + 1 : ℕ) : WithBot ℕ∞) := this
    exact Nat.le_of_succ_le_succ (by exact_mod_cast this)
  have : a.asIdeal.IsPrime := a.isPrime
  have hmin : ∀ f ∈ a.asIdeal, f ≠ 0 → a.asIdeal ∈ (Ideal.span {f}).minimalPrimes := fun f hf hf0 => by
    refine ⟨⟨a.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hf⟩, fun q' hq' hle => ?_⟩
    obtain ⟨hq'p, hlq'⟩ := hq'
    by_contra hne
    have hbot : (⊥ : Ideal A) ≠ q' := by
      intro h0
      have h1 : f ∈ q' := (Ideal.span_singleton_le_iff_mem _).1 hlq'
      rw [← h0, Ideal.mem_bot] at h1
      exact hf0 h1
    let b' : PrimeSpectrum A := ⟨q', hq'p⟩
    let g : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hsp (u v : PrimeSpectrum A) : j u ⤳ j v ↔ u.asIdeal ≤ v.asIdeal :=
      j.isOpenEmbedding.isInducing.specializes_iff.trans (PrimeSpectrum.le_iff_specializes u v).symm
    have h₁ : z < j b' := by
      rw [← ha]
      exact ⟨(hsp b' a).2 hle, fun h => hne ((hsp a b').1 h)⟩
    have h₂ : j b' < j g := ⟨(hsp g b').2 bot_le, fun h => hbot (le_bot_iff.1 ((hsp b' g).1 h)).symm⟩
    have h₃ := Order.coheight_add_one_le h₁
    have h₄ := Order.coheight_add_one_le h₂
    rw [hcoh] at h₃
    have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
    exact absurd h₅ (by decide)
  have hq := le_dim_quotient A a.asIdeal hmin hd
  have hlow : topologicalKrullDim (Set.range j ∩ closure {j a} : Set X) ≤
      topologicalKrullDim (closure ({z} : Set X)) := by
    rw [ha]
    exact (Topology.IsEmbedding.inclusion Set.inter_subset_right).isInducing.topologicalKrullDim_le
  rw [topologicalKrullDim_range_inter_closure_eq j a] at hlow
  replace hlow := hq.trans hlow
  obtain ⟨e, he⟩ : ∃ e : ℕ, topologicalKrullDim (closure ({z} : Set X)) = e :=
    have ⟨e, he⟩ := hX.exists_dim_eq i
    ⟨e, (topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hrange).trans he⟩
  rw [he] at hlow hup ⊢
  have h1 : d ≤ e := by exact_mod_cast hlow
  have h2 : e + 1 ≤ D + 1 := by exact_mod_cast hup
  have : e = D := by omega
  rw [this]

end ChowFormHeightComparison₂.CF
