import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters Formalism.L2.Pj

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Establish `hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤`. Introduce `h`. Establish `h1` using `congrArg Ideal.absNorm h`. Rewrite `h1` using `[Ideal.absNorm_span_singleton, Ideal.absNorm_top]`. Establish `: ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ)` using `by simp`.

Rewrite `h1` using `[this, Algebra.norm_algebraMap, RingOfIntegers.rank]`. Establish `hd : 0 < Module.finrank ℚ D.host.F` using `Module.finrank_pos`. Establish `hg` using `(D.host.g_prime j).two_le`. Rewrite `h1` using `[Int.natAbs_pow, Int.natAbs_natCast]`. Establish `: 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F` using `Nat.pow_le_pow_left hg _`.

Establish `: 2 ≤ 2 ^ Module.finrank ℚ D.host.F` using `Nat.le_self_pow hd.ne' 2`. Use linear arithmetic over natural numbers and integers. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P` using `hle (Ideal.mem_span_singleton_self _)`. Use `⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩` and prove the remaining obligations.

Rewrite `hg` using `[e, Ideal.mem_bot]`. Conclude with `(D.host.g_prime j).ne_zero (by exact_mod_cast hg)`.
-/
theorem exists_plOver (j : Fin 2) : Nonempty (PlOver D.host j) := by
  have hne : Ideal.span {((D.host.g j : ℕ) : 𝓞 D.host.F)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have : ((D.host.g j : ℕ) : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) (D.host.g j : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank] at h1
    have hd : 0 < Module.finrank ℚ D.host.F := Module.finrank_pos
    have hg := (D.host.g_prime j).two_le
    rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
    have : 2 ^ Module.finrank ℚ D.host.F ≤ D.host.g j ^ Module.finrank ℚ D.host.F := Nat.pow_le_pow_left hg _
    have : 2 ≤ 2 ^ Module.finrank ℚ D.host.F := Nat.le_self_pow hd.ne' 2
    omega
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
  have hg : ((D.host.g j : ℕ) : 𝓞 D.host.F) ∈ P := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨⟨P, hP.isPrime, fun e => ?_⟩, hg⟩⟩
  rw [e, Ideal.mem_bot] at hg
  exact (D.host.g_prime j).ne_zero (by exact_mod_cast hg)

/- English proof (translation)
Establish `ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id` using `hu.1.sub Matrix.blockTriangular_one`. Establish `hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r`. Rewrite using `[Matrix.charpoly_of_upperTriangular _ ht]`. Simplify using `[hu.2]`. Use `⟨r, ?_⟩` and prove the remaining obligations.

Use `Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)` as an intermediate fact. Rewrite `this` using `[hc, map_pow, Polynomial.aeval_X]`. Then use the resulting hypothesis.
-/
theorem isNilpotent_sub_one_of_unitri {r : ℕ} {k : Type} [Field k] {u : GL (Fin r) k} (hu : u ∈ unitri r k) :
    IsNilpotent ((u : Matrix (Fin r) (Fin r) k) - 1) := by
  have ht : ((u : Matrix (Fin r) (Fin r) k) - 1).BlockTriangular id := hu.1.sub Matrix.blockTriangular_one
  have hc : ((u : Matrix (Fin r) (Fin r) k) - 1).charpoly = Polynomial.X ^ r := by
    rw [Matrix.charpoly_of_upperTriangular _ ht]
    simp [hu.2]
  refine ⟨r, ?_⟩
  have := Matrix.aeval_self_charpoly ((u : Matrix (Fin r) (Fin r) k) - 1)
  rwa [hc, map_pow, Polynomial.aeval_X] at this

/- English proof (translation)
Establish `hP : (typePrime l v).IsPrime`. Use `halfPrime_isPrime l v.2.1.isMaximal ?_` and prove the remaining obligations. Take `⟨k, hk⟩` from `(g_dvd (D := D) v.1).trans hM`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ v.2.2`.

Use `⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v), fun hmem => ?_, hg v.1⟩, hP⟩` and prove the remaining obligations. Establish `h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `(D.host.g_prime v.1).ne_zero` after adjusting the coercions. Establish `hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)})` using `(UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2`.

Establish `hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]`. Conclude with `hmem`. Conclude with `hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))`.
-/
theorem neat_typePrime (hM : D.host.g 0 * D.host.g 1 ∣ l.M) (hg : ∀ k, Dw.p + Dw.q + 1 < D.host.g k)
    (v : Sq D.host) : NeatPrime (typePrime l v) (D.host.g v.1) (Dw.p + Dw.q) ∧ (typePrime l v).IsPrime := by
  have hP : (typePrime l v).IsPrime := by
    refine halfPrime_isPrime l v.2.1.isMaximal ?_
    obtain ⟨k, hk⟩ := (g_dvd (D := D) v.1).trans hM
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ v.2.2
  refine ⟨⟨D.host.g_prime v.1, absNorm_eq_of_split (D.host.g_prime _) (D.nd.g_split _) hP (g_mem_typePrime v),
    fun hmem => ?_, hg v.1⟩, hP⟩
  have h0 : Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime v.1).ne_zero
  have hsq : Squarefree (Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)}) :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors h0).2 (Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.g_splits D v.1).2
  have hd : typePrime l v * typePrime l v ∣ Ideal.span {((D.host.g v.1 : ℕ) : 𝓞 D.host.E)} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem, ← sq]
    exact hmem
  exact hP.ne_top (Ideal.isUnit_iff.1 (hsq _ hd))

/- English proof (translation)
Take `⟨n, hn⟩` from `isNilpotent_sub_one_of_unitri hγ`. Use `set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) := ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1 with hNm`. Set `π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v)` to `Submodule.mkQ _`. Establish `key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x))`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ m ih`. Introduce `x`.

Rewrite using `[pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]`. Generalize the expression as in `((liftLa γ - 1) ^ m) x = y`. Establish `h1 : π (liftLa γ y) = qProj (J` using `typePrime l v) le_sup_left (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by`. Rewrite using `[← liftLa_spec]`. Both sides reduce to the same expression.

Establish `h2 : π y = qProj (J` using `typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl`. Rewrite using `[LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec, Matrix.one_mulVec, typeRed_mulVec]`. Use `⟨n, fun x => ?_⟩` and prove the remaining obligations. Establish `h` using `key n x`. Rewrite `h` using `[hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff]`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).1 h`.
-/
theorem unipAt_of_unitri (fr : TypeFrame Dw l) (γ : LevelAut Dw l) (v : Sq D.host)
    (hγ : typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1))) : UnipAt (typePrime l v) γ := by
  obtain ⟨n, hn⟩ := isNilpotent_sub_one_of_unitri hγ
  set Nm : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1)) :=
    ((typeRed fr γ v : GL (Fin D.R.r) (ZMod (D.host.g v.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g v.1))) - 1
    with hNm
  let π : Dw.La →ₗ[𝓞 D.host.E] QMod Dw.La (typePrime l v) := Submodule.mkQ _
  have key : ∀ (m : ℕ) (x : Dw.La), fr v (π (((liftLa γ - 1) ^ m) x)) = (Nm ^ m).mulVec (fr v (π x)) := by
    intro m
    induction m with
    | zero => intro x; simp
    | succ m ih =>
      intro x
      rw [pow_succ', Module.End.mul_apply, pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      generalize ((liftLa γ - 1) ^ m) x = y
      have h1 : π (liftLa γ y) = qProj (J := typePrime l v) le_sup_left
          (γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y)) := by
        rw [← liftLa_spec]; rfl
      have h2 : π y = qProj (J := typePrime l v) le_sup_left ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ y) := rfl
      rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, map_sub, h1, h2, hNm, Matrix.sub_mulVec,
        Matrix.one_mulVec, typeRed_mulVec]
  refine ⟨n, fun x => ?_⟩
  have h := key n x
  rw [hn, Matrix.zero_mulVec, AddEquivClass.map_eq_zero_iff] at h
  exact (Submodule.Quotient.mk_eq_zero _).1 h

/- English proof (translation)
Break down `hS with rfl | ⟨k, rfl⟩` into its components or cases. Conclude with `⟨0, fun γ hγ v _ => hγ v trivial⟩`. Use `⟨k + 1, fun γ hγ v hv => hγ v ?_⟩ show v.1 ≠ k` and prove the remaining obligations. Apply the tactic sequence `rw [hv]; fin_cases k <;> decide`.
-/
theorem exists_index (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)) (hS : S = grpHR fr ∨ ∃ k, S = grpGHR fr k) :
    ∃ j : Fin 2, ∀ γ ∈ S, ∀ v : Sq D.host, v.1 = j → typeRed fr γ v ∈ unitri D.R.r (ZMod (D.host.g v.1)) := by
  rcases hS with rfl | ⟨k, rfl⟩
  · exact ⟨0, fun γ hγ v _ => hγ v trivial⟩
  · refine ⟨k + 1, fun γ hγ v hv => hγ v ?_⟩
    show v.1 ≠ k
    rw [hv]; fin_cases k <;> decide

end GlobalTheory.OrbitSep.UnipPrime

open GlobalTheory.OrbitSep.UnipPrime GlobalTheory.LevDesc GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters in

/- English proof (translation)
Introduce `D H Dw l hM hg fr S hS`. Take `⟨j, hj⟩` from `exists_index fr S hS`. Take `⟨w⟩` from `exists_plOver (D := D) j`. Set `v : Sq D.host` to `⟨j, w⟩`. Take `⟨hN, -⟩` from `neat_typePrime (Dw := Dw) hM hg v`.

Conclude with `⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩`.
-/
theorem GlobalTheory.OrbitSep.exists_neatPrime_unipAt : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H), D.host.g 0 * D.host.g 1 ∣ l.M → (∀ k, Dw.p + Dw.q + 1 < D.host.g k) → ∀ (fr : TypeFrame Dw l) (S : Subgroup (LevelAut Dw l)), (S = grpHR fr ∨ ∃ k, S = grpGHR fr k) → ∃ (I : Ideal (𝓞 D.host.E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) ∧ l.Mb ≤ I ∧ ∀ γ ∈ S, UnipAt I γ := by
  intro D H Dw l hM hg fr S hS
  obtain ⟨j, hj⟩ := exists_index fr S hS
  obtain ⟨w⟩ := exists_plOver (D := D) j
  let v : Sq D.host := ⟨j, w⟩
  obtain ⟨hN, -⟩ := neat_typePrime (Dw := Dw) hM hg v
  exact ⟨typePrime l v, D.host.g v.1, hN, le_sup_left, fun γ hγ => unipAt_of_unitri fr γ v (hj γ hγ v rfl)⟩
