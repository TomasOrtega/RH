import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

namespace TypesD

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Unfold `letE`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`.
-/
theorem letE_idem (c : ZMod n) : (letE (O := O) c : LetA O n) * letE c = letE c := by
  unfold letE
  funext i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

/- English proof (translation)
Unfold `letE`. Use `show ∀ δ ∈ W.DelF, (W.γA δ) (Pi.single c 1) = Pi.single c 1`. Introduce `δ hδ`. Unfold `LocWach.γA letγ`. Use function extensionality and compare the values at `i`.

Use `show (W.γ₀ δ) ((Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i) = (Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i`. Distinguish the cases in `h : i = c`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`.
-/
theorem letE_mem (c : ZMod n) : (letE (O := O) c : LetA O n) ∈ W.AΔ := by
  unfold letE
  show ∀ δ ∈ W.DelF, (W.γA δ) (Pi.single c 1) = Pi.single c 1
  intro δ hδ
  unfold LocWach.γA letγ
  funext i
  show (W.γ₀ δ) ((Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i) =
    (Pi.single c (1 : PowerSeries O) : ZMod n → PowerSeries O) i
  by_cases h : i = c
  · subst h; simp
  · simp [h]

/- English proof (translation)
Unfold `letE LocWach.φA letφ`. Use function extensionality and compare the values at `j`. Use `show W.φ₀ ((Pi.single i (1 : PowerSeries O) : ZMod n → PowerSeries O) (j - 1)) = (Pi.single (i + 1) (1 : PowerSeries O) : ZMod n → PowerSeries O) j`. Distinguish the cases in `h : j = i + 1`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `h' : j - 1 ≠ i` using `fun h' => h (by rw [← h']; ring)`. Simplify using `[h, h']`.
-/
theorem φA_letE (i : ZMod n) : W.φA (letE (O := O) i) = letE (i + 1) := by
  unfold letE LocWach.φA letφ
  funext j
  show W.φ₀ ((Pi.single i (1 : PowerSeries O) : ZMod n → PowerSeries O) (j - 1)) =
    (Pi.single (i + 1) (1 : PowerSeries O) : ZMod n → PowerSeries O) j
  by_cases h : j = i + 1
  · subst h; simp
  · have h' : j - 1 ≠ i := fun h' => h (by rw [← h']; ring)
    simp [h, h']

/- English proof (translation)
Establish `key : ∀ (a : LetA O n) (y : W.DD T), W.φD T (a • y) = W.φA a • W.φD T y`. Introduce `a y`. Establish `h` using `W.55 T (algebraMap (LetA O n) W.EE a) y`. Rewrite `h` using `[algebraMap_smul]`. Rewrite using `[h, ← algebraMap_smul W.EE (W.φA a)]`.

Use `congr 1`. Conclude with `W.44 a`. Use `conv_rhs => rw [← hx]`. Rewrite using `[key, φA_letE]`.
-/
theorem φD_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T}
    (hx : (letE (O := O) i : LetA O n) • x = x) :
    (letE (O := O) (i + 1) : LetA O n) • W.φD T x = W.φD T x := by
  have key : ∀ (a : LetA O n) (y : W.DD T), W.φD T (a • y) = W.φA a • W.φD T y := by
    intro a y
    have h := W.55 T (algebraMap (LetA O n) W.EE a) y
    rw [algebraMap_smul] at h
    rw [h, ← algebraMap_smul W.EE (W.φA a)]
    congr 1
    exact W.44 a
  conv_rhs => rw [← hx]
  rw [key, φA_letE]

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simpa using hx`. Consider the case `succ e ih`. Rewrite using `[pow_succ']`. Use `show (letE (O := O) (i + ((e + 1 : ℕ) : ZMod n)) : LetA O n) • W.φD T (((W.φD T) ^ e) x) = W.φD T (((W.φD T) ^ e) x)`.

Rewrite using `[Nat.cast_succ, ← add_assoc]`. Conclude with `φD_letter W ih`.
-/
theorem φDpow_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T}
    (hx : (letE (O := O) i : LetA O n) • x = x) (e : ℕ) :
    (letE (O := O) (i + (e : ZMod n)) : LetA O n) • ((W.φD T) ^ e) x = ((W.φD T) ^ e) x := by
  induction e with
  | zero => simpa using hx
  | succ e ih =>
    rw [pow_succ']
    show (letE (O := O) (i + ((e + 1 : ℕ) : ZMod n)) : LetA O n) • W.φD T (((W.φD T) ^ e) x) =
      W.φD T (((W.φD T) ^ e) x)
    rw [Nat.cast_succ, ← add_assoc]
    exact φD_letter W ih

/- English proof (translation)
Unfold `LocWach.Nl at hx`. Take `⟨y, -, rfl⟩` from `hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← mul_smul, letE_idem]`.
-/
private theorem letE_smul_of_mem_Nl' {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T i) :
    (letE (O := O) i : LetA O n) • x = x := by
  unfold LocWach.Nl at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← mul_smul, letE_idem]

/- English proof (translation)
Take `⟨y, -, rfl⟩` from `h`. Establish `hbm : ∀ m, (letE (O` using `O) c' : LetA O n) • b m = b m := fun m => letE_smul_of_mem_Nl' W (hb.1.1 m).2`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun r _ => ?_)` and prove the remaining obligations. Rewrite using `[← mul_smul, mul_comm, mul_smul]`.

Use `congr 1`. Unfold `Formalism.MainNotions.LiftingTheory.vecB`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Use `first`.

Consider the case `rw [smul_comm, hbm m]`. Consider the case `rw [← algebraMap_smul (LetA O n) (y r m) (b m), ← mul_smul, mul_comm, mul_smul, hbm m]`.
-/
theorem horTr_letter {T : LocLat G Qp LL O} {c' : ZMod n} {d : ℕ} {b : Fin d → W.DD T}
    {sol : Fin d → ℕ → Fin d → LL} (hb : IsHor W T c' b sol) {R κ : ℕ} {k : Fin d} {x : W.DD T}
    (h : IsHorTr W T b sol R κ k x) : (letE (O := O) c' : LetA O n) • x = x := by
  obtain ⟨y, -, rfl⟩ := h
  have hbm : ∀ m, (letE (O := O) c' : LetA O n) • b m = b m := fun m => letE_smul_of_mem_Nl' W (hb.1.1 m).2
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← mul_smul, mul_comm, mul_smul]
  congr 1
  unfold Formalism.MainNotions.LiftingTheory.vecB
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  first
  | rw [smul_comm, hbm m]
  | rw [← algebraMap_smul (LetA O n) (y r m) (b m), ← mul_smul, mul_comm, mul_smul, hbm m]

end TypesD

/- English proof (translation)
Unfold `LiftsAtT at h ⊢`. Take `⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a, hH, ha, hR⟩` from `h`. Use `⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, fun k => letE c * a k, hH, fun k => ⟨mul_mem (TypesD.letE_mem W c) (ha k).1, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `hak` using `(ha k).2 beta_reduce at hak ⊢`. Apply the tactic sequence `have hfk : (if k = k₀ then lE W e * (algebraMap (LetA O n) W.EE (letE c) * f) else 0) = algebraMap (LetA O n) W.EE (letE c) * (if k = k₀ then lE W e * f else 0) := by split_ifs <;> ring`.

Rewrite using `[hfk, map_mul, ← hak]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : ∑ k, (letE (O` using `O) c * a k) • ((W.φD T₂) ^ (A.len c)) (H k) = ∑ k, a k • ((W.φD T₂) ^ (A.len c)) (H k) := by`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul, smul_comm]`.

Use `congr 1`. Use `TypesD.φDpow_letter W (TypesD.horTr_letter W hb (hH k)) (A.len c)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Use `beta_reduce`. Rewrite using `[hs]`.

Conclude with `hR`.
-/
theorem LiftsAtT.letter (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) {f : W.EE} {e : ℕ}
    (h : LiftsAtT W A F c b sol k₀ f e) :
    LiftsAtT W A F c b sol k₀ (algebraMap (LetA O n) W.EE (letE c) * f) e := by
  unfold LiftsAtT at h ⊢
  obtain ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, a, hH, ha, hR⟩ := h
  refine ⟨w₁, z, hw, hΛ, hP, hz, κ, κ', H, fun k => letE c * a k, hH,
    fun k => ⟨mul_mem (TypesD.letE_mem W c) (ha k).1, ?_⟩, ?_⟩
  · have hak := (ha k).2
    beta_reduce at hak ⊢
    have hfk : (if k = k₀ then lE W e * (algebraMap (LetA O n) W.EE (letE c) * f) else 0) =
        algebraMap (LetA O n) W.EE (letE c) * (if k = k₀ then lE W e * f else 0) := by
      split_ifs <;> ring
    rw [hfk, map_mul, ← hak]
    ring
  · have hs : ∑ k, (letE (O := O) c * a k) • ((W.φD T₂) ^ (A.len c)) (H k) =
        ∑ k, a k • ((W.φD T₂) ^ (A.len c)) (H k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_smul, smul_comm]
      congr 1
      have := TypesD.φDpow_letter W (TypesD.horTr_letter W hb (hH k)) (A.len c)
      rwa [sub_add_cancel] at this
    beta_reduce
    rw [hs]
    exact hR

namespace TypesD

variable (W : LocWach PD LL O v n)

/- English proof (translation)
Unfold `LocWach.Nl at hx`. Take `⟨y, -, rfl⟩` from `hx`. Simplify using `only [LinearMap.smul_apply, LinearMap.id_apply]`. Rewrite using `[← mul_smul, letE_idem]`.
-/
theorem nl_letter {T : LocLat G Qp LL O} {i : ZMod n} {x : W.DD T} (hx : x ∈ W.Nl T i) :
    (letE (O := O) i : LetA O n) • x = x := by
  unfold LocWach.Nl at hx
  obtain ⟨y, -, rfl⟩ := hx
  simp only [LinearMap.smul_apply, LinearMap.id_apply]
  rw [← mul_smul, letE_idem]

/- English proof (translation)
Unfold `cmpD`. Establish `hs : ∑ m, y m ∈ W.N T` using `Submodule.sum_mem _ (fun m _ => hy m)`. Rewrite using `[dif_pos hs]`. Use `conv_rhs => arg 2`. Use extensionality with `m`.

Rewrite using `[dif_pos (hy m)]`. Rewrite using `[← map_sum]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
theorem cmpD_sum {T : LocLat G Qp LL O} {d : ℕ} (y : Fin d → W.DD T) (hy : ∀ m, y m ∈ W.N T) :
    cmpD W T (∑ m, y m) = ∑ m, cmpD W T (y m) := by
  unfold cmpD
  have hs : ∑ m, y m ∈ W.N T := Submodule.sum_mem _ (fun m _ => hy m)
  rw [dif_pos hs]
  conv_rhs => arg 2; ext m; rw [dif_pos (hy m)]
  rw [← map_sum]
  congr 1
  apply Subtype.ext
  simp

/- English proof (translation)
Use `set c₀ : O := PowerSeries.constantCoeff (a i) with hc₀`. Set `r : LetA O n` to `fun _ => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i)`. Establish `hring : a * letE i = (algebraMap O (LetA O n) c₀ + letπ * r) * letE i`. Use function extensionality and compare the values at `j`. Simplify using `only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one, mul_one, Pi.algebraMap_apply, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Simplify using `only [letπ, r]`. Rewrite using `[add_comm]`.

Conclude with `PowerSeries.eq_X_mul_shift_add_const (a j)`. Rewrite using `[mul_zero, mul_zero]`. Establish `hid : a • y = c₀ • y + (letπ : LetA O n) • (r • y)`. Rewrite using `[← algebraMap_smul (LetA O n) c₀ y, smul_smul, ← add_smul]`. Use `conv_lhs => rw [← hy, smul_smul, hring]`.

Rewrite using `[← smul_smul, hy]`. Establish `hay : a • y ∈ W.N T` using `(W.N T).smul_mem a hyN`. Establish `hry : r • y ∈ W.N T` using `(W.N T).smul_mem r hyN`. Establish `he : (⟨a • y, hay⟩ : W.N T) = c₀ • (⟨y, hyN⟩ : W.N T) + (letπ : LetA O n) • (⟨r • y, hry⟩ : W.N T)`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_add, Submodule.coe_smul_of_tower]`. Conclude with `hid`. Rewrite using `[cmpD, dif_pos hay, he, map_add, W.cmp_smul, W.cmp_π, add_zero, cmpD, dif_pos hyN]`.
-/
theorem cmpD_smul_letter {T : LocLat G Qp LL O} {i : ZMod n} (a : LetA O n) {y : W.DD T} (hyN : y ∈ W.N T)
    (hy : (letE (O := O) i : LetA O n) • y = y) :
    cmpD W T (a • y) = algebraMap O LL (PowerSeries.constantCoeff (a i)) • cmpD W T y := by
  set c₀ : O := PowerSeries.constantCoeff (a i) with hc₀
  let r : LetA O n := fun _ => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i)
  have hring : a * letE i = (algebraMap O (LetA O n) c₀ + letπ * r) * letE i := by
    funext j
    simp only [Pi.mul_apply, Pi.add_apply, letE, Pi.single_apply]
    split_ifs with h
    · subst h
      rw [mul_one, mul_one, Pi.algebraMap_apply, PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      simp only [letπ, r]
      rw [add_comm]
      exact PowerSeries.eq_X_mul_shift_add_const (a j)
    · rw [mul_zero, mul_zero]
  have hid : a • y = c₀ • y + (letπ : LetA O n) • (r • y) := by
    rw [← algebraMap_smul (LetA O n) c₀ y, smul_smul, ← add_smul]
    conv_lhs => rw [← hy, smul_smul, hring]
    rw [← smul_smul, hy]
  have hay : a • y ∈ W.N T := (W.N T).smul_mem a hyN
  have hry : r • y ∈ W.N T := (W.N T).smul_mem r hyN
  have he : (⟨a • y, hay⟩ : W.N T) = c₀ • (⟨y, hyN⟩ : W.N T) + (letπ : LetA O n) • (⟨r • y, hry⟩ : W.N T) := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul_of_tower]
    exact hid
  rw [cmpD, dif_pos hay, he, map_add, W.cmp_smul, W.cmp_π, add_zero, cmpD, dif_pos hyN]

end TypesD

/- English proof (translation)
Establish `hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts` using `(hA.2.2.1 c hc).2.2.1`. Take `⟨d₁, b₁, sol₁, hb₁⟩` from `hHF hcase hl A hA T₁ hW₁ (c - ((A.len c : ℕ) : ZMod n))`. Take `⟨⟨hfr₂, -⟩, -⟩` from `hb`. Establish `hb₁'` using `hb₁`. Take `⟨⟨hfr₁, huniq₁⟩, -⟩` from `hb₁'`.

Take `⟨x₁, hx₁, hmap⟩` from `hArcL hcase T₁ T₂ F hsur _ rr (A.len c) (hrr _ hc') (b k₀) (hfr₂ k₀)`. Take `⟨a, ⟨-, hx⟩, -⟩` from `huniq₁ x₁ hx₁`. Establish `hN : ∀ m, b₁ m ∈ W.N T₁` using `fun m => (hfr₁ m).1.1`. Establish `hL : ∀ m, (letE (O` using `O) (c - ((A.len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m := fun m => TypesD.nl_letter W (hfr₁ m).2`. Establish `hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) • cmpD W T₁ (b₁ m)`.

Rewrite using `[hx, TypesD.cmpD_sum W _ fun m => (W.N T₁).smul_mem _ (hN m)]`. Conclude with `Finset.sum_congr rfl fun m _ => TypesD.cmpD_smul_letter W (a m) (hN m) (hL m)`. Use `⟨d₁, b₁, sol₁, fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n))), hb₁, ?_⟩` and prove the remaining obligations. Establish `hdv1 : dvO W T₁ (A.len c) b₁ (fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) = ((φVB PD (LL` using `LL) (V := T₁.V)) ^ (A.len c)) (cmpD W T₁ x₁) := by`. Rewrite using `[hcmp, map_sum]`.

Simplify using `only [dvO, dv, map_smul]`. Establish `hdv2 : dv W T₂ (A.len c) b (Pi.single k₀ 1) = ((φVB PD (LL` using `LL) (V := T₂.V)) ^ (A.len c)) (cmpD W T₂ (b k₀)) := by`. Unfold `dv`. Rewrite using `[Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ _) h)]`. Simplify using the standard rewrite rules.

Rewrite using `[hdv1, hdv2]`. Conclude with `hmap`.
-/
theorem constants_pre (hA : A.OK) (hc : c ∈ A.cuts) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hl : 5 ≤ PD.p)
    (hHF : HorFrameCoreT W) (hArcL : ArcLCore W) (hW₁ : Win W A T₁) (hsur : Formalism.MainNotions.LiftingTheory.Sur W F)
    (rr : ℕ) (hrr : ∀ c'' ∈ A.cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c'' (Formalism.MainNotions.LiftingTheory.lp W rr))
    (hb : IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol) :
    ∃ (d₁ : ℕ) (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL) (c₁ : Fin d₁ → O),
      IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁ ∧
      Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dvO W T₁ (A.len c) b₁ c₁) =
        ((PD.p : LL) ^ rr) • dv W T₂ (A.len c) b (Pi.single k₀ 1) := by
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := (hA.2.2.1 c hc).2.2.1
  obtain ⟨d₁, b₁, sol₁, hb₁⟩ := hHF hcase hl A hA T₁ hW₁ (c - ((A.len c : ℕ) : ZMod n))
  obtain ⟨⟨hfr₂, -⟩, -⟩ := hb
  have hb₁' := hb₁
  obtain ⟨⟨hfr₁, huniq₁⟩, -⟩ := hb₁'
  obtain ⟨x₁, hx₁, hmap⟩ := hArcL hcase T₁ T₂ F hsur _ rr (A.len c) (hrr _ hc') (b k₀) (hfr₂ k₀)
  obtain ⟨a, ⟨-, hx⟩, -⟩ := huniq₁ x₁ hx₁
  have hN : ∀ m, b₁ m ∈ W.N T₁ := fun m => (hfr₁ m).1.1
  have hL : ∀ m, (letE (O := O) (c - ((A.len c : ℕ) : ZMod n)) : LetA O n) • b₁ m = b₁ m :=
    fun m => TypesD.nl_letter W (hfr₁ m).2
  have hcmp : cmpD W T₁ x₁ = ∑ m, algebraMap O LL (PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) •
      cmpD W T₁ (b₁ m) := by
    rw [hx, TypesD.cmpD_sum W _ fun m => (W.N T₁).smul_mem _ (hN m)]
    exact Finset.sum_congr rfl fun m _ => TypesD.cmpD_smul_letter W (a m) (hN m) (hL m)
  refine ⟨d₁, b₁, sol₁, fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n))), hb₁, ?_⟩
  have hdv1 : dvO W T₁ (A.len c) b₁ (fun m => PowerSeries.constantCoeff (a m (c - ((A.len c : ℕ) : ZMod n)))) =
      ((φVB PD (LL := LL) (V := T₁.V)) ^ (A.len c)) (cmpD W T₁ x₁) := by
    rw [hcmp, map_sum]
    simp only [dvO, dv, map_smul]
  have hdv2 : dv W T₂ (A.len c) b (Pi.single k₀ 1) =
      ((φVB PD (LL := LL) (V := T₂.V)) ^ (A.len c)) (cmpD W T₂ (b k₀)) := by
    unfold dv
    rw [Finset.sum_eq_single k₀ (fun m _ hm => by simp [hm]) (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [hdv1, hdv2]
  exact hmap

end Formalism.MainNotions.N.FrobeniusPowerSeries
