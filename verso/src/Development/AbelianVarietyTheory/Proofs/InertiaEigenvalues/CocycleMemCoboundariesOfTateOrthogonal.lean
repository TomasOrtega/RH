import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeDualPairingCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMutuallyDualStableLatticesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateOrthV

/- English proof (translation)
Establish `hχ : ∀ g, ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b`. Introduce `g`. Use `Formalism.MainNotions.BlochKatoDuality.Br.zl_int hO _ ?_` and prove the remaining obligations. Rewrite using `[P.PD_χ K g]`. Take `⟨a, ha, _⟩` from `P.χQ_cyc (g : GQ l) 0 1 (one_pow _)`.

Establish `h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) = (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l])`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Use `(Padic.nonarchimedean _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Simplify using `using ha`.

Conclude with `Padic.norm_int_le_one (a : ℤ)` after adjusting the coercions. Take `⟨⟨hD, hV, hF⟩, _⟩` from `id hO`. Use `⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩` and prove the remaining obligations. Introduce and unpack `g _ ⟨x, rfl⟩`. Take `⟨b, hb⟩` from `hχ g`.

Use `⟨b * x, ?_⟩` and prove the remaining obligations. Use `show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x`. Rewrite using `[map_mul, hb, smul_eq_mul]`. Rewrite using `[← Submodule.map_top]`. Conclude with `Submodule.FG.map _ Module.Finite.fg_top`.

Conclude with `Module.Free.of_equiv (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `h1 : (1 : LL) ∈ Submodule.span LL ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL)` using `Submodule.subset_span ⟨1, by simp⟩`. Simplify using `using Submodule.smul_mem _ x h1`.
-/
theorem exists_unitLattice {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type)
    [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL]
    (hO : GoodO (Qp := ℚ_[l]) LL O) :
    ∃ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)),
      L1.T = LinearMap.range (Algebra.linearMap O LL) := by
  have hχ : ∀ g, ∃ b : O, ((cycLL (P.PD K) LL g : LLˣ) : LL) = algebraMap O LL b := by
    intro g
    refine Formalism.MainNotions.BlochKatoDuality.Br.zl_int hO _ ?_
    rw [P.PD_χ K g]
    obtain ⟨a, ha, _⟩ := P.χQ_cyc (g : GQ l) 0 1 (one_pow _)
    have h1 : ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) =
        (((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) - (a : ℚ_[l])) + (a : ℚ_[l]) := by
      ring
    rw [h1]
    refine (Padic.nonarchimedean _ _).trans (max_le ?_ ?_)
    · simpa using ha
    · exact_mod_cast Padic.norm_int_le_one (a : ℤ)
  obtain ⟨⟨hD, hV, hF⟩, _⟩ := id hO
  refine ⟨⟨LinearMap.range (Algebra.linearMap O LL), ?_, ?_, ?_, ?_⟩, rfl⟩
  · rintro g _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := hχ g
    refine ⟨b * x, ?_⟩
    show algebraMap O LL (b * x) = ((cycLL (P.PD K) LL g : LLˣ) : LL) • algebraMap O LL x
    rw [map_mul, hb, smul_eq_mul]
  · rw [← Submodule.map_top]
    exact Submodule.FG.map _ Module.Finite.fg_top
  · exact Module.Free.of_equiv
      (LinearEquiv.ofInjective (Algebra.linearMap O LL) (IsFractionRing.injective O LL))
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ Submodule.span LL
        ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) :=
      Submodule.subset_span ⟨1, by simp⟩
    simpa using Submodule.smul_mem _ x h1

/- English proof (translation)
Introduce `hT l _ P K LL _ _ _ O _ _ hO A A' m hm b hb horth`. Take `⟨⟨hDom, hDVR, hFrac⟩, hfd, hmt, htr, hopen⟩` from `id hO`. Use `haveI := hDom`. Use `haveI := hDVR`. Use `haveI := hFrac`.

Use `haveI := htr`. Use `haveI : IsTopologicalAddGroup A'.V := IsModuleTopology.topologicalAddGroup LL A'.V`. Take `⟨L1, hL1⟩` from `exists_unitLattice P K LL O hO`. Take `⟨LA, LA', hLL', -⟩` from `GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm`. Establish `hT'open : IsOpen (LA'.T : Set A'.V)` using `Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA'.T LA'.fg LA'.span`.

Establish `hL1open : IsOpen (L1.T : Set LL)`. Rewrite using `[hL1]`. Establish `e : ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) = Set.range (algebraMap O LL)`. Use extensionality with `y`. Simplify using `[Algebra.linearMap_apply]`.

Rewrite using `[e]`. Conclude with `hopen`. Establish `hp : ((l : ℕ) : LL) ≠ 0`. Rewrite using `[← map_natCast (algebraMap ℚ_[l] LL)]`. Conclude with `(map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)`.

Establish `hcobZ : ∀ x : A'.V, (fun g => A'.ρ g x - x) ∈ continuousCocycles A'.ρ`. Introduce `x`. Use `⟨(A'.cont x).sub continuous_const, fun g h => ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, Module.End.mul_apply, map_sub]`. Normalize the expressions using the abelian group laws.

Establish `key : ∀ n : ℕ, ∃ β ∈ latticeCocycles LA', b - ((l : LL) ^ n) • β ∈ B1 A'.ρ`. Introduce `n`. Use `set s : LL := (((l : ℕ) : LL) ^ n)⁻¹ with hs`. Set `c : ↥(GK K) → A'.V ⧸ LA'.T` to `fun g => Submodule.Quotient.mk (s • b g)`. Establish `hcZ : c ∈ divisibleCocycles LA'`.

Use `⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA'.T hT'open _ (hb.1.const_smul s), fun g h => ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (s • b (g * h)) = Submodule.Quotient.mk (s • b g) + actD LA' g (Submodule.Quotient.mk (s • b h))`. Rewrite using `[hb.2 g h, smul_add, Submodule.Quotient.mk_add]`. Use `congr 1`. Use `show _ = Submodule.Quotient.mk (A'.ρ g (s • b h))`.

Rewrite using `[map_smul]`. Establish `hcorth : ∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c)`. Introduce `d hd`. Take `⟨f, hfc, hf⟩` from `horth d hd.1`. Use `⟨fun g => (Submodule.Quotient.mk (s • f g) : LL ⧸ L1.T), ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hL1open _ (hfc.const_smul s), fun _ => Submodule.mem_top⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Take `⟨g, h⟩` from `x`. Establish `hf' : ((cycLL (P.PD K) LL g : LLˣ) : LL) • f h - f (g * h) + f g = m (d g) (A'.ρ g (b h))` using `congrFun hf (g, h)`. Establish `hlift : liftD LA' (c h) - s • b h ∈ LA'.T` using `(Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec`. Take `⟨e, he⟩` from `(hLL'.2 _).1 (LA'.stable g _ hlift) (d g) (hd.2 g (Set.mem_univ g))`.

Use `show (Submodule.Quotient.mk (((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h)) : LL ⧸ L1.T) - Submodule.Quotient.mk (s • f (g * h)) + Submodule.Quotient.mk (s • f g) = Submodule.Quotient.mk (m (d g) (A'.ρ g (liftD LA' (c h))))`. Rewrite using `[← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hL1]`. Establish `e1 : ((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h) - s • f (g * h) + s • f g = s • m (d g) (A'.ρ g (b h))`. Rewrite using `[← hf']`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : m (d g) (A'.ρ g (liftD LA' (c h))) = s • m (d g) (A'.ρ g (b h)) + m (d g) (A'.ρ g (liftD LA' (c h) - s • b h))`. Simplify using `only [map_sub, map_smul, add_sub_cancel]`. Rewrite using `[e1, e2]`. Use `⟨-e, ?_⟩` and prove the remaining obligations.

Use `show algebraMap O LL (-e) = _`. Rewrite using `[map_neg, ← he]`. Normalize the expressions using the abelian group laws. Take `⟨xbar, hx⟩` from `GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m hLL' c hcZ hcorth`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective LA'.T xbar`.

Use `⟨fun g => s • b g - (A'.ρ g x - x), ⟨(continuousCocycles A'.ρ).sub_mem ((continuousCocycles A'.ρ).smul_mem s hb) (hcobZ x), fun g _ => ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hg : Submodule.Quotient.mk (A'.ρ g x) - Submodule.Quotient.mk x = (Submodule.Quotient.mk (s • b g) : A'.V ⧸ LA'.T)` using `congrFun hx g`. Rewrite `hg` using `[← Submodule.Quotient.mk_sub]`. Conclude with `(Submodule.Quotient.eq _).1 hg.symm`. Use `⟨(((l : ℕ) : LL) ^ n) • x, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Establish `hps : (((l : ℕ) : LL) ^ n) * s = 1` using `mul_inv_cancel₀ (pow_ne_zero n hp)`. Simplify using `only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul, Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, hps, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hl : ((l : ℕ) : O) ∉ nonunits O → False`.

Introduce `hu`. Establish `hu' : IsUnit ((l : ℕ) : O)` using `by simpa [mem_nonunits_iff] using hu`. Establish `hc` using `(GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.2`. Establish `htop : Ideal.span {((l : ℕ) : O)} = ⊤` using `Ideal.span_singleton_eq_top.2 hu'`. Establish `h10 : (1 : O) = 0`.

Apply `hc.toIsHausdorff.haus 1` to reduce the goal to its premises. Introduce `n`. Rewrite using `[htop, Ideal.top_pow, Submodule.top_smul]`. Conclude with `SModEq.top`. Conclude with `one_ne_zero h10`.

Establish `hne : Ideal.span {((l : ℕ) : O)} ≠ ⊤`. Introduce `htop`. Apply `hl` to reduce the goal to its premises. Introduce `hmem`. Conclude with `hmem (Ideal.span_singleton_eq_top.1 htop)`.

Use `haveI hfinH : Module.Finite O (LatticeCohomology LA') := GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'`. Set `S : Submodule O ↥(latticeCocycles LA')` to `((B1 A'.ρ).restrictScalars O).comap (latticeCocycles LA').subtype`. Establish `hBS : (latticeCoboundaries LA').comap (latticeCocycles LA').subtype ≤ S`. Introduce and unpack `z ⟨y, -, hy⟩`. Conclude with `⟨y, hy⟩`.

Use `haveI : Module.Finite O (↥(latticeCocycles LA') ⧸ S) := by`. Use `Module.Finite.of_surjective (Submodule.factor hBS) ?_` and prove the remaining obligations. Introduce `q`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Conclude with `⟨Submodule.Quotient.mk z, rfl⟩`.

Establish `hK` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥(latticeCocycles LA') ⧸ S) _ hne`. Take `⟨β0, hβ0, hbβ0⟩` from `key 0`. Rewrite `hbβ0` using `[pow_zero, one_smul]`. Establish `hq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = 0`. Rewrite using `[← Submodule.mem_bot O, ← hK, Submodule.mem_iInf]`.

Introduce `i`. Take `⟨β, hβ, hbβ⟩` from `key i`. Establish `heq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = (((l : ℕ) : O) ^ i) • Submodule.Quotient.mk ⟨β, hβ⟩`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]`. Use `show β0 - (((l : ℕ) : O) ^ i) • β ∈ B1 A'.ρ`.

Establish `h1 : β0 - (((l : ℕ) : O) ^ i) • β = (b - ((l : LL) ^ i) • β) - (b - β0)`. Rewrite using `[← algebraMap_smul LL (((l : ℕ) : O) ^ i) β, map_pow, map_natCast]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Conclude with `(B1 A'.ρ).sub_mem hbβ hbβ0`.

Rewrite using `[heq, Ideal.span_singleton_pow]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top`. Establish `hβ0B : β0 ∈ B1 A'.ρ` using `(Submodule.Quotient.mk_eq_zero S).1 hq`. Establish `: b = (b - β0) + β0` using `by abel`. Rewrite using `[this]`.

Conclude with `(B1 A'.ρ).add_mem hbβ0 hβ0B`.
-/
theorem cocycle_mem_coboundaries_of_tate_orthogonal' : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDual1 (P.PD K) A.ρ A'.ρ m → ∀ b ∈ continuousCocycles A'.ρ, (∀ a ∈ continuousCocycles A.ρ, CobL (P.PD K) (cupL A'.ρ m a b)) → b ∈ B1 A'.ρ := by
  intro hT l _ P K LL _ _ _ O _ _ hO A A' m hm b hb horth
  obtain ⟨⟨hDom, hDVR, hFrac⟩, hfd, hmt, htr, hopen⟩ := id hO
  haveI := hDom; haveI := hDVR; haveI := hFrac; haveI := htr
  haveI : IsTopologicalAddGroup A'.V := IsModuleTopology.topologicalAddGroup LL A'.V
  obtain ⟨L1, hL1⟩ := exists_unitLattice P K LL O hO
  obtain ⟨LA, LA', hLL', -⟩ := GlobalTheory.T.exists_mutuallyDual_stable_lattices l P K LL O hO A A' m hm
  have hT'open : IsOpen (LA'.T : Set A'.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA'.T LA'.fg LA'.span
  have hL1open : IsOpen (L1.T : Set LL) := by
    rw [hL1]
    have e : ((LinearMap.range (Algebra.linearMap O LL) : Submodule O LL) : Set LL) =
        Set.range (algebraMap O LL) := by
      ext y; simp [Algebra.linearMap_apply]
    rw [e]; exact hopen
  have hp : ((l : ℕ) : LL) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] LL)]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

  have hcobZ : ∀ x : A'.V, (fun g => A'.ρ g x - x) ∈ continuousCocycles A'.ρ := by
    intro x
    refine ⟨(A'.cont x).sub continuous_const, fun g h => ?_⟩
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel

  have key : ∀ n : ℕ, ∃ β ∈ latticeCocycles LA', b - ((l : LL) ^ n) • β ∈ B1 A'.ρ := by
    intro n
    set s : LL := (((l : ℕ) : LL) ^ n)⁻¹ with hs
    let c : ↥(GK K) → A'.V ⧸ LA'.T := fun g => Submodule.Quotient.mk (s • b g)
    have hcZ : c ∈ divisibleCocycles LA' := by
      refine ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA'.T hT'open _ (hb.1.const_smul s), fun g h => ?_⟩
      show Submodule.Quotient.mk (s • b (g * h)) = Submodule.Quotient.mk (s • b g) +
        actD LA' g (Submodule.Quotient.mk (s • b h))
      rw [hb.2 g h, smul_add, Submodule.Quotient.mk_add]
      congr 1
      show _ = Submodule.Quotient.mk (A'.ρ g (s • b h))
      rw [map_smul]
    have hcorth : ∀ d ∈ latticeCocycles LA, CobO (P.PD K) L1 (cupLD LA' m d c) := by
      intro d hd
      obtain ⟨f, hfc, hf⟩ := horth d hd.1
      refine ⟨fun g => (Submodule.Quotient.mk (s • f g) : LL ⧸ L1.T),
        ⟨Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hL1open _ (hfc.const_smul s), fun _ => Submodule.mem_top⟩, ?_⟩
      funext x
      obtain ⟨g, h⟩ := x
      have hf' : ((cycLL (P.PD K) LL g : LLˣ) : LL) • f h - f (g * h) + f g =
          m (d g) (A'.ρ g (b h)) := congrFun hf (g, h)
      have hlift : liftD LA' (c h) - s • b h ∈ LA'.T :=
        (Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_surjective LA'.T (c h)).choose_spec
      obtain ⟨e, he⟩ := (hLL'.2 _).1 (LA'.stable g _ hlift) (d g) (hd.2 g (Set.mem_univ g))
      show (Submodule.Quotient.mk (((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h)) : LL ⧸ L1.T) -
          Submodule.Quotient.mk (s • f (g * h)) + Submodule.Quotient.mk (s • f g) =
          Submodule.Quotient.mk (m (d g) (A'.ρ g (liftD LA' (c h))))
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, hL1]
      have e1 : ((cycLL (P.PD K) LL g : LLˣ) : LL) • (s • f h) - s • f (g * h) + s • f g =
          s • m (d g) (A'.ρ g (b h)) := by
        rw [← hf']; simp only [smul_eq_mul]; ring
      have e2 : m (d g) (A'.ρ g (liftD LA' (c h))) =
          s • m (d g) (A'.ρ g (b h)) + m (d g) (A'.ρ g (liftD LA' (c h) - s • b h)) := by
        simp only [map_sub, map_smul, add_sub_cancel]
      rw [e1, e2]
      refine ⟨-e, ?_⟩
      show algebraMap O LL (-e) = _
      rw [map_neg, ← he]
      abel
    obtain ⟨xbar, hx⟩ := GlobalTheory.TateOrth.mem_BD_of_orthogonal hT l P K LL O hO L1 hL1 A A' LA LA' m
      hLL' c hcZ hcorth
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective LA'.T xbar
    refine ⟨fun g => s • b g - (A'.ρ g x - x), ⟨(continuousCocycles A'.ρ).sub_mem ((continuousCocycles A'.ρ).smul_mem s hb) (hcobZ x),
      fun g _ => ?_⟩, ?_⟩
    · have hg : Submodule.Quotient.mk (A'.ρ g x) - Submodule.Quotient.mk x =
          (Submodule.Quotient.mk (s • b g) : A'.V ⧸ LA'.T) := congrFun hx g
      rw [← Submodule.Quotient.mk_sub] at hg
      exact (Submodule.Quotient.eq _).1 hg.symm
    · refine ⟨(((l : ℕ) : LL) ^ n) • x, ?_⟩
      funext g
      have hps : (((l : ℕ) : LL) ^ n) * s = 1 := mul_inv_cancel₀ (pow_ne_zero n hp)
      simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_smul,
        Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul, hps, one_smul]
      abel

  have hl : ((l : ℕ) : O) ∉ nonunits O → False := by
    intro hu
    have hu' : IsUnit ((l : ℕ) : O) := by simpa [mem_nonunits_iff] using hu
    have hc := (GlobalTheory.GoodCoeff.good_coeff_integers l LL O hO).2.2.2
    have htop : Ideal.span {((l : ℕ) : O)} = ⊤ := Ideal.span_singleton_eq_top.2 hu'
    have h10 : (1 : O) = 0 := by
      apply hc.toIsHausdorff.haus 1
      intro n
      rw [htop, Ideal.top_pow, Submodule.top_smul]
      exact SModEq.top
    exact one_ne_zero h10
  have hne : Ideal.span {((l : ℕ) : O)} ≠ ⊤ := by
    intro htop
    apply hl
    intro hmem
    exact hmem (Ideal.span_singleton_eq_top.1 htop)
  haveI hfinH : Module.Finite O (LatticeCohomology LA') :=
    GlobalTheory.TateFiniteH1.tate_finH1 hT l P K LL O hO A' LA'
  let S : Submodule O ↥(latticeCocycles LA') := ((B1 A'.ρ).restrictScalars O).comap (latticeCocycles LA').subtype
  have hBS : (latticeCoboundaries LA').comap (latticeCocycles LA').subtype ≤ S := by
    rintro z ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  haveI : Module.Finite O (↥(latticeCocycles LA') ⧸ S) := by
    refine Module.Finite.of_surjective (Submodule.factor hBS) ?_
    intro q
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hK := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := ↥(latticeCocycles LA') ⧸ S) _ hne
  obtain ⟨β0, hβ0, hbβ0⟩ := key 0
  rw [pow_zero, one_smul] at hbβ0
  have hq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) = 0 := by
    rw [← Submodule.mem_bot O, ← hK, Submodule.mem_iInf]
    intro i
    obtain ⟨β, hβ, hbβ⟩ := key i
    have heq : (Submodule.Quotient.mk ⟨β0, hβ0⟩ : ↥(latticeCocycles LA') ⧸ S) =
        (((l : ℕ) : O) ^ i) • Submodule.Quotient.mk ⟨β, hβ⟩ := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show β0 - (((l : ℕ) : O) ^ i) • β ∈ B1 A'.ρ
      have h1 : β0 - (((l : ℕ) : O) ^ i) • β = (b - ((l : LL) ^ i) • β) - (b - β0) := by
        rw [← algebraMap_smul LL (((l : ℕ) : O) ^ i) β, map_pow, map_natCast]
        abel
      rw [h1]
      exact (B1 A'.ρ).sub_mem hbβ hbβ0
    rw [heq, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  have hβ0B : β0 ∈ B1 A'.ρ := (Submodule.Quotient.mk_eq_zero S).1 hq
  have : b = (b - β0) + β0 := by abel
  rw [this]
  exact (B1 A'.ρ).add_mem hbβ0 hβ0B

end GlobalTheory.TateOrthV
