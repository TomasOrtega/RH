import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.GradNPfA

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

/- English proof (translation)
Use `show r₀ ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r₀ = r₀`. Use `⟨hr₀N, fun δ hδ => ?_⟩` and prove the remaining obligations. Establish `h1` using `hΔ δ hδ`. Rewrite `h1` using `[← algebraMap_smul W.EE (π' ^ k) r₀, W.γD_smul, W.γE_ext]`. Establish `e : Formalism.BasicNotions.letγ (W.γ₀ δ) (π' ^ k) = π' ^ k`.

Express the relevant statement in the definitionally equal form `W.γA δ (π' ^ k) = π' ^ k`. Rewrite using `[map_pow, hπΔ δ hδ]`. Rewrite `h1` using `[e]`. Establish `hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k))`. Rewrite using `[map_pow]`.

Conclude with `hu.pow k`. Conclude with `hu'.smul_left_cancel.mp h1`.
-/
theorem invLiftPf_quot_Δ (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π') (k : ℕ) (r₀ : W.DD T) (hr₀N : r₀ ∈ W.N T)
    (hΔ : ∀ δ ∈ W.DelF, W.γD T δ (π' ^ k • r₀) = π' ^ k • r₀) : r₀ ∈ W.NΔ T := by
  show r₀ ∈ W.N T ∧ ∀ δ ∈ W.DelF, W.γD T δ r₀ = r₀
  refine ⟨hr₀N, fun δ hδ => ?_⟩
  have h1 := hΔ δ hδ
  rw [← algebraMap_smul W.EE (π' ^ k) r₀, W.γD_smul, W.γE_ext] at h1
  have e : Formalism.BasicNotions.letγ (W.γ₀ δ) (π' ^ k) = π' ^ k := by
    change W.γA δ (π' ^ k) = π' ^ k
    rw [map_pow, hπΔ δ hδ]
  rw [e] at h1
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by
    rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h1

/- English proof (translation)
Unfold `PiNS`. Rewrite using `[Submodule.mem_inf]`. Use `and_congr ?_ Iff.rfl` and prove the remaining obligations. Use `show x ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ k)) ↔ _`. Rewrite using `[Submodule.mem_map]`.

Both sides reduce to the same expression.
-/
private theorem PiNS_iff_lemma_3 (π' : LetA O n) (k : ℕ) (x : W.DD T) :
    x ∈ PiNS W T π' k ↔ (∃ y ∈ W.N T, π' ^ k • y = x) ∧ x ∈ DelS W T := by
  unfold PiNS
  rw [Submodule.mem_inf]
  refine and_congr ?_ Iff.rfl
  show x ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ k)) ↔ _
  rw [Submodule.mem_map]
  rfl

/- English proof (translation)
Unfold `DelS`. Simplify using `[Submodule.mem_iInf, sub_eq_zero]`.
-/
private theorem DelS_iff_lemma_4 (x : W.DD T) : x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  unfold DelS
  simp [Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Use `show W.γD T g (a • x) = Formalism.BasicNotions.letγ (W.γ₀ g) a • W.γD T g x`. Rewrite using `[← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]`.
-/
private theorem gamD_smulA_lemma_5 (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = Formalism.BasicNotions.letγ (W.γ₀ g) a • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

/- English proof (translation)
Rewrite `h` using `[← algebraMap_smul W.EE (π' ^ k) u, ← algebraMap_smul W.EE (π' ^ k) v]`. Establish `hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k))` using `by rw [map_pow]; exact hu.pow k`. Conclude with `hu'.smul_left_cancel.mp h`.
-/
private theorem cancel_lemma_6 (π' : LetA O n) (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (k : ℕ)
    (u v : W.DD T) (h : π' ^ k • u = π' ^ k • v) : u = v := by
  rw [← algebraMap_smul W.EE (π' ^ k) u, ← algebraMap_smul W.EE (π' ^ k) v] at h
  have hu' : IsUnit (algebraMap (LetA O n) W.EE (π' ^ k)) := by rw [map_pow]; exact hu.pow k
  exact hu'.smul_left_cancel.mp h

/- English proof (translation)
Take `⟨⟨y, hy, hyz⟩, hzD⟩` from `(PiNS_iff_lemma_3 W T π' b z).mp hz`. Use `(PiNS_iff_lemma_3 W T π' a z).mpr ⟨⟨π' ^ (b - a) • y, (W.N T).smul_mem _ hy, ?_⟩, hzD⟩` and prove the remaining obligations. Rewrite using `[← hyz, smul_smul, ← pow_add, show a + (b - a) = b by omega]`.
-/
private theorem PiNS_anti_lemma_7 (π' : LetA O n) {a b : ℕ} (hab : a ≤ b) {z : W.DD T}
    (hz : z ∈ PiNS W T π' b) : z ∈ PiNS W T π' a := by
  obtain ⟨⟨y, hy, hyz⟩, hzD⟩ := (PiNS_iff_lemma_3 W T π' b z).mp hz
  refine (PiNS_iff_lemma_3 W T π' a z).mpr ⟨⟨π' ^ (b - a) • y, (W.N T).smul_mem _ hy, ?_⟩, hzD⟩
  rw [← hyz, smul_smul, ← pow_add, show a + (b - a) = b by omega]

/- English proof (translation)
Establish `hx'` using `(PiNS_iff_lemma_3 W T π' 1 x).mp hx`. Establish `hxD : x ∈ DelS W T` using `hx'.2`. Establish `hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x` using `(DelS_iff_lemma_4 W T x).mp hxD`. Take `⟨x₁, hx₁, hx₁x⟩` from `hx'.1`. Establish `hxN : x ∈ W.N T` using `by rw [← hx₁x]; exact (W.N T).smul_mem _ hx₁`.

Rewrite `hgx` using `[hK]`. Establish `key : ∀ y : ℕ, y ≤ M → x ∈ PiNS W T π' y`. Introduce `y`. Proceed by induction on `y with`. Consider the case `zero`.

Introduce `_`. Conclude with `(PiNS_iff_lemma_3 W T π' 0 x).mpr ⟨⟨x, hxN, by simp⟩, hxD⟩`. Consider the case `succ y ih`. Introduce `hyM`. Break down `Nat.eq_zero_or_pos y with hy0 | hy0` into its components or cases.

Substitute `hy0` using the available equality. Conclude with `hx`. Take `⟨⟨r₀, hr₀, hr₀x⟩, -⟩` from `(PiNS_iff_lemma_3 W T π' y x).mp (ih (by omega))`. Establish `hr₀Δ : r₀ ∈ W.NΔ T` using `invLiftPf_quot_Δ W T π' hu hπΔ y r₀ hr₀ (fun δ hδ => by rw [hr₀x]; exact hxΔ δ hδ)`. Take `⟨d, hd, hdγ⟩` from `hγN r₀ hr₀Δ`.

Establish `hγr : W.γD T W.gam r₀ = r₀ + π' • d` using `sub_eq_iff_eq_add'.mp hdγ`. Take `⟨s, hs⟩ : π' ∣ f ^ y - algebraMap O (LetA O n) c₀ ^ y` from `(Dvd.intro t ht.symm).trans (sub_dvd_pow_sub_pow _ _ _)`. Establish `hfy : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * s` using `by rw [← hs]; ring`. Establish `hg'` using `PiNS_anti_lemma_7 W T π' hyM hgx`. Take `⟨⟨e', he', he'x⟩, -⟩` from `(PiNS_iff_lemma_3 W T π' (y + 1) _).mp hg'`.

Establish `hγx : W.γD T W.gam x - x = π' ^ y • (algebraMap O (LetA O n) (c₀ ^ y - 1) • r₀ + π' • (s • r₀ + f ^ y • d))`. Rewrite using `[← hr₀x, gamD_smulA_lemma_5, map_pow, hf, hγr, mul_pow, hfy, map_sub, map_pow, map_one]`. Use `set a : LetA O n := algebraMap O (LetA O n) c₀ with ha_def`. Establish `e1 : ∀ (A B A' B' : LetA O n), A = A' → B = B' → A • r₀ + B • d = A' • r₀ + B' • d`. Introduce `A B A' B' h1 h2`.

Rewrite using `[h1, h2]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_add, sub_smul, smul_smul]`. Normalize the expressions using the abelian group laws. Use `_ = (π' ^ y * (a ^ y - 1) + π' ^ y * (π' * s)) • r₀ + (π' ^ y * (π' * (a ^ y + π' * s))) • d := e1 _ _ _ _ (by ring) (by ring)`.

Use `_ = _ := by`. Simplify using `only [smul_add, smul_smul, add_smul, add_assoc, mul_add]`. Rewrite `he'x` using `[hγx, pow_succ, ← smul_smul]`. Establish `h1` using `cancel_lemma_6 W T π' hu y _ _ he'x`. Establish `h2 : (c₀ ^ y - 1) • r₀ = π' • (e' - (s • r₀ + f ^ y • d))`.

Rewrite using `[← algebraMap_smul (LetA O n) (c₀ ^ y - 1) r₀, smul_sub, h1]`. Normalize the expressions using the abelian group laws. Take `⟨e, he, hre⟩` from `hnz y hy0 (by omega) r₀ hr₀ _ (Submodule.sub_mem _ he' (Submodule.add_mem _ ((W.N T).smul_mem _ hr₀) ((W.N T).smul_mem _ hd))) h2`. Use `(PiNS_iff_lemma_3 W T π' (y + 1) x).mpr ⟨⟨e, he, ?_⟩, hxD⟩` and prove the remaining obligations. Rewrite using `[← hr₀x, hre, smul_smul, ← pow_succ]`.

Conclude with `key M le_rfl`.
-/
theorem invLiftPf_inj (π' f t : LetA O n) (c₀ : O) (hf : W.γA W.gam π' = π' * f)
    (ht : f - algebraMap O (LetA O n) c₀ = π' * t)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hπΔ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hγN : ∀ x ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam x - x = π' • d)
    (hK : W.gamK = W.gam) (M : ℕ)
    (hnz : ∀ y : ℕ, 1 ≤ y → y < M → ∀ r₀ ∈ W.N T, ∀ d ∈ W.N T,
      (c₀ ^ y - 1) • r₀ = π' • d → ∃ e ∈ W.N T, r₀ = π' • e)
    (x : W.DD T) (hx : x ∈ PiNS W T π' 1) (hgx : W.γD T W.gamK x - x ∈ PiNS W T π' M) :
    x ∈ PiNS W T π' M := by
  have hx' := (PiNS_iff_lemma_3 W T π' 1 x).mp hx
  have hxD : x ∈ DelS W T := hx'.2
  have hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x := (DelS_iff_lemma_4 W T x).mp hxD
  obtain ⟨x₁, hx₁, hx₁x⟩ := hx'.1
  have hxN : x ∈ W.N T := by rw [← hx₁x]; exact (W.N T).smul_mem _ hx₁
  rw [hK] at hgx
  have key : ∀ y : ℕ, y ≤ M → x ∈ PiNS W T π' y := by
    intro y
    induction y with
    | zero =>
      intro _
      exact (PiNS_iff_lemma_3 W T π' 0 x).mpr ⟨⟨x, hxN, by simp⟩, hxD⟩
    | succ y ih =>
      intro hyM
      rcases Nat.eq_zero_or_pos y with hy0 | hy0
      · subst hy0; exact hx
      · obtain ⟨⟨r₀, hr₀, hr₀x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' y x).mp (ih (by omega))
        have hr₀Δ : r₀ ∈ W.NΔ T :=
          invLiftPf_quot_Δ W T π' hu hπΔ y r₀ hr₀ (fun δ hδ => by rw [hr₀x]; exact hxΔ δ hδ)
        obtain ⟨d, hd, hdγ⟩ := hγN r₀ hr₀Δ
        have hγr : W.γD T W.gam r₀ = r₀ + π' • d := sub_eq_iff_eq_add'.mp hdγ
        obtain ⟨s, hs⟩ : π' ∣ f ^ y - algebraMap O (LetA O n) c₀ ^ y :=
          (Dvd.intro t ht.symm).trans (sub_dvd_pow_sub_pow _ _ _)
        have hfy : f ^ y = algebraMap O (LetA O n) c₀ ^ y + π' * s := by rw [← hs]; ring
        have hg' := PiNS_anti_lemma_7 W T π' hyM hgx
        obtain ⟨⟨e', he', he'x⟩, -⟩ := (PiNS_iff_lemma_3 W T π' (y + 1) _).mp hg'
        have hγx : W.γD T W.gam x - x = π' ^ y • (algebraMap O (LetA O n) (c₀ ^ y - 1) • r₀ +
            π' • (s • r₀ + f ^ y • d)) := by
          rw [← hr₀x, gamD_smulA_lemma_5, map_pow, hf, hγr, mul_pow, hfy, map_sub, map_pow, map_one]
          set a : LetA O n := algebraMap O (LetA O n) c₀ with ha_def
          have e1 : ∀ (A B A' B' : LetA O n), A = A' → B = B' → A • r₀ + B • d = A' • r₀ + B' • d := by
            intro A B A' B' h1 h2; rw [h1, h2]
          calc _ = (π' ^ y * (a ^ y + π' * s) - π' ^ y) • r₀ + (π' ^ y * (a ^ y + π' * s) * π') • d := by
                  rw [smul_add, sub_smul, smul_smul]; abel
            _ = (π' ^ y * (a ^ y - 1) + π' ^ y * (π' * s)) • r₀ +
                  (π' ^ y * (π' * (a ^ y + π' * s))) • d := e1 _ _ _ _ (by ring) (by ring)
            _ = _ := by
              simp only [smul_add, smul_smul, add_smul, add_assoc, mul_add]
        rw [hγx, pow_succ, ← smul_smul] at he'x
        have h1 := cancel_lemma_6 W T π' hu y _ _ he'x
        have h2 : (c₀ ^ y - 1) • r₀ = π' • (e' - (s • r₀ + f ^ y • d)) := by
          rw [← algebraMap_smul (LetA O n) (c₀ ^ y - 1) r₀, smul_sub, h1]
          abel
        obtain ⟨e, he, hre⟩ := hnz y hy0 (by omega) r₀ hr₀ _
          (Submodule.sub_mem _ he' (Submodule.add_mem _ ((W.N T).smul_mem _ hr₀)
            ((W.N T).smul_mem _ hd))) h2
        refine (PiNS_iff_lemma_3 W T π' (y + 1) x).mpr ⟨⟨e, he, ?_⟩, hxD⟩
        rw [← hr₀x, hre, smul_smul, ← pow_succ]
  exact key M le_rfl

/- English proof (translation)
Establish `hℓm : ∀ k : ℕ, ∀ c : O, ℓ ^ k * c = 0 → c = 0`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro c hc`. Simplify using `using hc`.

Consider the case `succ k ih => intro c hc`. Rewrite `hc` using `[pow_succ, mul_assoc]`. Conclude with `hℓ _ (ih _ hc)`. Take `⟨a, ha, -⟩` from `huniq r₀ hr₀`. Take `⟨cc, hc, -⟩` from `huniq y hy`.

Establish `hmem : ℓ ^ m • r₀ ∈ W.N T`. Rewrite using `[← algebraMap_smul (LetA O n) (ℓ ^ m) r₀]`. Conclude with `(W.N T).smul_mem _ hr₀`. Establish `e1 : ℓ ^ m • r₀ = ∑ j, (algebraMap O (LetA O n) (ℓ ^ m) * a j) • b j`. Rewrite using `[ha, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul (LetA O n) (ℓ ^ m), smul_smul]`. Establish `e2 : ℓ ^ m • r₀ = ∑ j, (π' * cc j) • b j`. Rewrite using `[h, hc, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul]`. Establish `hcoef : (fun j => algebraMap O (LetA O n) (ℓ ^ m) * a j) = fun j => π' * cc j` using `(huniq _ hmem).unique e1 e2`. Establish `hdiv : ∀ j i, ∃ e : PowerSeries O, a j i = PowerSeries.X ^ s' * e`. Introduce `j i`. Establish `h1 : (algebraMap O (LetA O n) (ℓ ^ m) * a j) i = (π' * cc j) i` using `congrFun (congrFun hcoef j) i`.

Rewrite `h1` using `[hπ]`. Establish `h3 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i = (w i * PowerSeries.X ^ s') * cc j i` using `h1`. Establish `h2 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i = PowerSeries.X ^ s' * (w i * cc j i)`. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4 : ∀ d < s', PowerSeries.coeff d (a j i) = 0`. Introduce `d hd`. Establish `h5 : PowerSeries.coeff d (algebraMap O (PowerSeries O) (ℓ ^ m) * a j i) = 0`. Rewrite using `[h2]`. Conclude with `PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) d hd`.

Rewrite `h5` using `[← Algebra.smul_def, PowerSeries.coeff_smul, smul_eq_mul]`. Conclude with `hℓm m _ h5`. Conclude with `PowerSeries.X_pow_dvd_iff.mpr h4`. Use `choose e he using hdiv`. Take `⟨u, hu⟩` from `hw`.

Establish `hA : ∀ j, a j = π' * ((↑u⁻¹ : LetA O n) * fun i => e j i)`. Introduce `j`. Establish `hx : π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) = letπ ^ s' * fun i => e j i`. Rewrite using `[hπ, ← hu, show ((↑u : LetA O n) * letπ ^ s') * ((↑u⁻¹ : LetA O n) * fun i => e j i) = ((↑u : LetA O n) * ↑u⁻¹) * (letπ ^ s' * fun i => e j i) by ring, Units.mul_inv, one_mul]`. Rewrite using `[hx]`.

Use function extensionality and compare the values at `i`. Conclude with `he j i`. Use `⟨∑ j, ((↑u⁻¹ : LetA O n) * fun i => e j i) • b j, Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbN j), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum, ha]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_smul, ← hA j]`.
-/
theorem invLiftPf_nzd (π' w : LetA O n) (s' : ℕ) (hw : IsUnit w) (hπ : π' = w * letπ ^ s')
    (ℓ : O) (hℓ : ∀ c : O, ℓ * c = 0 → c = 0)
    (r : ℕ) (b : Fin r → W.DD T) (hbN : ∀ j, b j ∈ W.N T)
    (huniq : ∀ x ∈ W.N T, ∃! a : Fin r → LetA O n, x = ∑ j, a j • b j)
    (m : ℕ) (r₀ y : W.DD T) (hr₀ : r₀ ∈ W.N T) (hy : y ∈ W.N T)
    (h : ℓ ^ m • r₀ = π' • y) : ∃ e ∈ W.N T, r₀ = π' • e := by
  classical
  have hℓm : ∀ k : ℕ, ∀ c : O, ℓ ^ k * c = 0 → c = 0 := by
    intro k
    induction k with
    | zero => intro c hc; simpa using hc
    | succ k ih => intro c hc; rw [pow_succ, mul_assoc] at hc; exact hℓ _ (ih _ hc)
  obtain ⟨a, ha, -⟩ := huniq r₀ hr₀
  obtain ⟨cc, hc, -⟩ := huniq y hy
  have hmem : ℓ ^ m • r₀ ∈ W.N T := by
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m) r₀]; exact (W.N T).smul_mem _ hr₀
  have e1 : ℓ ^ m • r₀ = ∑ j, (algebraMap O (LetA O n) (ℓ ^ m) * a j) • b j := by
    rw [ha, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul (LetA O n) (ℓ ^ m), smul_smul]
  have e2 : ℓ ^ m • r₀ = ∑ j, (π' * cc j) • b j := by
    rw [h, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
  have hcoef : (fun j => algebraMap O (LetA O n) (ℓ ^ m) * a j) = fun j => π' * cc j :=
    (huniq _ hmem).unique e1 e2
  have hdiv : ∀ j i, ∃ e : PowerSeries O, a j i = PowerSeries.X ^ s' * e := by
    intro j i
    have h1 : (algebraMap O (LetA O n) (ℓ ^ m) * a j) i = (π' * cc j) i :=
      congrFun (congrFun hcoef j) i
    rw [hπ] at h1
    have h3 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        (w i * PowerSeries.X ^ s') * cc j i := h1
    have h2 : algebraMap O (PowerSeries O) (ℓ ^ m) * a j i =
        PowerSeries.X ^ s' * (w i * cc j i) := by
      rw [h3]; ring
    have h4 : ∀ d < s', PowerSeries.coeff d (a j i) = 0 := by
      intro d hd
      have h5 : PowerSeries.coeff d (algebraMap O (PowerSeries O) (ℓ ^ m) * a j i) = 0 := by
        rw [h2]; exact PowerSeries.X_pow_dvd_iff.mp (dvd_mul_right _ _) d hd
      rw [← Algebra.smul_def, PowerSeries.coeff_smul, smul_eq_mul] at h5
      exact hℓm m _ h5
    exact PowerSeries.X_pow_dvd_iff.mpr h4
  choose e he using hdiv
  obtain ⟨u, hu⟩ := hw
  have hA : ∀ j, a j = π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) := by
    intro j
    have hx : π' * ((↑u⁻¹ : LetA O n) * fun i => e j i) = letπ ^ s' * fun i => e j i := by
      rw [hπ, ← hu, show ((↑u : LetA O n) * letπ ^ s') * ((↑u⁻¹ : LetA O n) * fun i => e j i)
        = ((↑u : LetA O n) * ↑u⁻¹) * (letπ ^ s' * fun i => e j i) by ring, Units.mul_inv, one_mul]
    rw [hx]
    funext i
    exact he j i
  refine ⟨∑ j, ((↑u⁻¹ : LetA O n) * fun i => e j i) • b j,
    Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (hbN j), ?_⟩
  rw [Finset.smul_sum, ha]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← hA j]

/- English proof (translation)
Unfold `letS`. Rewrite using `[LinearMap.mem_ker]`. Simplify using `[sub_eq_zero]`.
-/
private theorem letS_mem_lemma (c : ZMod n) (x : W.DD T) :
    x ∈ letS W T c ↔ (letE c : LetA O n) • x = x := by
  unfold letS
  rw [LinearMap.mem_ker]
  simp [sub_eq_zero]

/- English proof (translation)
Establish `e : Formalism.BasicNotions.letγ (W.γ₀ g) (letE c : LetA O n) = letE c`. Use function extensionality and compare the values at `i`. Use `show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i`. Unfold `letE`. Distinguish the cases in `hi : i = c`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hi]`. Rewrite using `[← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, e, algebraMap_smul]`.
-/
private theorem gam_letE_lemma_2 (g : W.Gam) (c : ZMod n) (x : W.DD T) :
    W.γD T g ((letE c : LetA O n) • x) = (letE c : LetA O n) • W.γD T g x := by
  have e : Formalism.BasicNotions.letγ (W.γ₀ g) (letE c : LetA O n) = letE c := by
    funext i
    show W.γ₀ g ((letE c : LetA O n) i) = (letE c : LetA O n) i
    unfold letE
    by_cases hi : i = c
    · subst hi; simp
    · simp [Pi.single_apply, hi]
  rw [← algebraMap_smul W.EE (letE c : LetA O n) x, W.γD_smul, W.γE_ext, e, algebraMap_smul]

/- English proof (translation)
Introduce `w hw`. Unfold `InvS at hw ⊢`. Rewrite `hw` using `[Submodule.mem_inf, Submodule.mem_comap]`. Take `⟨hwL, hwγ⟩` from `hw`. Rewrite `hwγ` using `[LinearMap.sub_apply, LinearMap.id_apply]`.

Establish `hwS : w ∈ letS W T c`. Establish `h0` using `hwL`. Unfold `LamPS at h0`. Conclude with `(Submodule.mem_inf.mp h0).2`. Establish `hzS : W.γD T W.gamK w - w ∈ letS W T c`.

Rewrite `hwS`, the goal using `[letS_mem_lemma]`. Rewrite using `[smul_sub, ← gam_letE_lemma_2, hwS]`. Take `⟨k, hk, hk2⟩` from `hG c (W.γD T W.gamK w - w) (Submodule.mem_inf.mpr ⟨hwγ, hzS⟩)`. Take `⟨hk1, hkS⟩` from `Submodule.mem_inf.mp hk`. Use `⟨((PD.p : ℕ) : O) ^ σ • w - k, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_inf]`. Use `⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hwL) (hL c ?_), ?_⟩` and prove the remaining obligations. Unfold `NcS`. Use `Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, hkS⟩` and prove the remaining obligations. Establish `h0` using `hk1`.

Unfold `PiNS at h0`. Establish `h1 : k ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ 1))` using `(Submodule.mem_inf.mp h0).1`. Take `⟨y, hy, hyk⟩` from `Submodule.mem_map.mp h1`. Rewrite using `[← hyk]`. Conclude with `(W.N T).smul_mem _ hy`.

Establish `h0` using `hk1`. Unfold `PiNS at h0`. Conclude with `(Submodule.mem_inf.mp h0).2`. Rewrite using `[Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_smul]`. Use `hk2 using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[sub_sub_cancel]`. Conclude with `hk1`.
-/
theorem invLiftPf_lift (π' Eπ : LetA O n) (h' M σ : ℕ) (c : ZMod n)
    (hG : GradN W T π' σ M) (hL : NinLam W T Eπ h') :
    ∀ w ∈ InvS W T π' Eπ h' 1 c, ∃ wb ∈ InvS W T π' Eπ h' M c,
      ((PD.p : ℕ) : O) ^ σ • w - wb ∈ PiNS W T π' 1 := by
  intro w hw
  unfold InvS at hw ⊢
  rw [Submodule.mem_inf, Submodule.mem_comap] at hw
  obtain ⟨hwL, hwγ⟩ := hw
  rw [LinearMap.sub_apply, LinearMap.id_apply] at hwγ
  have hwS : w ∈ letS W T c := by
    have h0 := hwL
    unfold LamPS at h0
    exact (Submodule.mem_inf.mp h0).2
  have hzS : W.γD T W.gamK w - w ∈ letS W T c := by
    rw [letS_mem_lemma] at hwS ⊢
    rw [smul_sub, ← gam_letE_lemma_2, hwS]
  obtain ⟨k, hk, hk2⟩ := hG c (W.γD T W.gamK w - w) (Submodule.mem_inf.mpr ⟨hwγ, hzS⟩)
  obtain ⟨hk1, hkS⟩ := Submodule.mem_inf.mp hk
  refine ⟨((PD.p : ℕ) : O) ^ σ • w - k, ?_, ?_⟩
  · rw [Submodule.mem_inf]
    refine ⟨Submodule.sub_mem _ (Submodule.smul_mem _ _ hwL) (hL c ?_), ?_⟩
    · unfold NcS
      refine Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨?_, ?_⟩, hkS⟩
      · have h0 := hk1
        unfold PiNS at h0
        have h1 : k ∈ (W.N T).map (Formalism.MainNotions.DeltaInvariantLattices.smulA W T (π' ^ 1)) := (Submodule.mem_inf.mp h0).1
        obtain ⟨y, hy, hyk⟩ := Submodule.mem_map.mp h1
        rw [← hyk]
        exact (W.N T).smul_mem _ hy
      · have h0 := hk1
        unfold PiNS at h0
        exact (Submodule.mem_inf.mp h0).2
    · rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply, map_sub, map_smul]
      convert hk2 using 1
      rw [smul_sub]
      abel
  · rw [sub_sub_cancel]
    exact hk1

end Local

end Formalism.MainNotions.N.Ln34

end
