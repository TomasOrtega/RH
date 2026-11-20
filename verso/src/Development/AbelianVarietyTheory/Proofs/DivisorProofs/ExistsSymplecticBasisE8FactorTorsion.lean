import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsE8WeightedBundle
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSharpBasisSharpBasis
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsStdSympZmod
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis

/- English proof (translation)
Use `set σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm with hσ`. Establish `l : ∀ a, (σ.symm (.inl a) : ℕ) = a` using `fun _ => rfl`. Establish `r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a` using `fun _ => rfl`. Establish `ll : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inl j)) = 0` using `fun i j => by`. Use `i.2` as an intermediate fact.

Use `j.2` as an intermediate fact. Apply the tactic sequence `simp only [Out.stdSymp, l, r]; split_ifs <;> omega`. Establish `rr : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inr j)) = 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Apply the tactic sequence `simp only [Out.stdSymp, l, r]; split_ifs <;> omega`. Establish `lr : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inr j)) = if i = j then 1 else 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Apply the tactic sequence `simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega`.

Establish `rl : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inl j)) = if i = j then -1 else 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact. Apply the tactic sequence `simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega`. Simplify using `only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]`.

Simplify using `[sub_eq_add_neg]`.
-/
theorem omegaStd_eq_sum (g : ℕ) (a b : Fin g ⊕ Fin g → ℤ) :
    omegaStd a b = ∑ c, ∑ d, Out.stdSymp g (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm c)
      (((finCongr (two_mul g)).trans finSumFinEquiv.symm).symm d) * (a c * b d) := by
  set σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm with hσ
  have l : ∀ a, (σ.symm (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (σ.symm (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r]; split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (σ.symm (.inl i)) (σ.symm (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (σ.symm (.inr i)) (σ.symm (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]; split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg]

/- English proof (translation)
Set `s₀ : Fin 8 → ℤ` to `Pi.single 0 1`. Set `t₀ : Fin 8 → ℤ` to `E.adjugate.mulVec s₀`. Establish `h₀ : dotProduct s₀ (E.mulVec t₀) = 1`. Simplify using `only [t₀, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]`. Simplify using `[s₀]`.

Establish `h₀' : dotProduct t₀ (E.mulVec s₀) = 1`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hE, dotProduct_comm, h₀]`. Set `pw : (Fin 8 → ℤ) → T →* (Fin 8 → T)` to `fun s => MonoidHom.mk' (fun p u => p ^ s u) fun p q => funext fun u => mul_zpow p q _`. Set `h : T →* T →* Rˣ` to `((e.comp (pw s₀)).flip.comp (pw t₀)).flip`. Establish `hh : ∀ p q, h p q = e (fun u => p ^ s₀ u) (fun u => q ^ t₀ u)` using `fun _ _ => rfl`.

Establish `key : ∀ (s t : Fin 8 → ℤ) (p q : T), e (fun u => p ^ s u) (fun u => q ^ t u) = h p q ^ dotProduct s (E.mulVec t)` using `fun s t p q => by`. Rewrite using `[hrel s t (dotProduct s (E.mulVec t) • s₀) t₀ (by rw [smul_dotProduct, h₀, smul_eq_mul, _root_.mul_one]), hh, ← MonoidHom.zpow_apply, ← map_zpow]`. Use `congr 2`. Use function extensionality and compare the values at `u`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.pow_apply]`.

Rewrite using `[← zpow_mul, _root_.mul_comm]`. Establish `eskew : ∀ x y, e x y * e y x = 1` using `fun x y => by`. Use `halt (x * y)` as an intermediate fact. Simplify using `only [map_mul, MonoidHom.mul_apply, halt, _root_.one_mul, _root_.mul_one] at this`. Apply the tactic sequence `first | exact this | (rw [_root_.mul_comm]; exact this)`.

Establish `halt' : ∀ p, h p p = 1` using `fun p => by`. Establish `k₁ : h p p ^ 2 = 1`. Use `eskew (fun u => p ^ s₀ u) (fun u => p ^ t₀ u)` as an intermediate fact. Rewrite `this` using `[key, key, h₀, h₀', zpow_one, ← pow_two]`. Then use the resulting hypothesis. Establish `k₂ : h p p ^ N = 1` using `by rw [← map_pow, hT, map_one]`.

Take `⟨m, rfl⟩` from `hN`. Rewrite `k₂` using `[pow_succ, pow_mul, k₁, one_pow, _root_.one_mul]`. Then use the resulting hypothesis. Establish `hnd' : ∀ p, (∀ q, h p q = 1) → p = 1` using `fun p hp => by`. Use `hnd (fun u => p ^ s₀ u) fun y => by` as an intermediate fact. Establish `hy : y = ∏ v, fun u => y v ^ (Pi.single v 1 : Fin 8 → ℤ) u`.

Use function extensionality and compare the values at `u`. Rewrite using `[Finset.prod_apply, Finset.prod_eq_single u (fun v _ hv => by simp [Pi.single_apply, hv.symm]) (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[hy, map_prod]`. Conclude with `Finset.prod_eq_one fun v _ => by rw [key, hp, one_zpow]`.

Simplify `congrFun this 0` using `[s₀]`. Take `⟨v, hv⟩` from `exists_stdSymp_of_alternating_pairing N g T R z hN.pos hz hT hc h halt' hnd'`. Set `σ : Fin (2 * g) ≃ Fin g ⊕ Fin g` to `(finCongr (two_mul g)).trans finSumFinEquiv.symm`. Use `⟨fun c => v (σ.symm c), fun x y => ?_⟩` and prove the remaining obligations. Establish `hp : ∀ x : Fin 8 → (Fin g ⊕ Fin g → ℤ), (fun u => ∏ c, v (σ.symm c) ^ x u c) = ∏ c, fun u => v (σ.symm c) ^ x u c` using `fun x =>`.

Use function extensionality and compare the values at `fun u => by rw [Finset.prod_apply]`. Rewrite using `[hp, hp]`. Simplify using `only [map_prod, MonoidHom.finset_prod_apply, key, hv, ← zpow_mul]`. Establish `zs : ∀ {α : Type} [Fintype α] (f : α → ℤ), ∏ a, z ^ f a = z ^ ∑ a, f a` using `fun f => (map_prod (zpowersHom Rˣ z) (fun a => Multiplicative.ofAdd (f a)) Finset.univ).symm`. Simplify using `only [zs]`.

Use `congr 1`. Simplify using `only [omegaStd_eq_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `(Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans (Finset.sum_congr rfl fun u _ => ?_))` and prove the remaining obligations. Use `(Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans (Finset.sum_congr rfl fun u' _ => ?_))` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `only [σ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_family {N g : ℕ} (hN : Odd N) {T R : Type} [CommGroup T] [CommRing R] [IsDomain R] {z : Rˣ}
    (hz : IsPrimitiveRoot z N) (hT : ∀ x : T, x ^ N = 1)
    (hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g))
    (E : Matrix (Fin 8) (Fin 8) ℤ) (hE : E.transpose = E) (hdet : E.det = 1)
    (e : (Fin 8 → T) →* (Fin 8 → T) →* Rˣ) (halt : ∀ x, e x x = 1) (hnd : ∀ x, (∀ y, e x y = 1) → x = 1)
    (hrel : ∀ s t s' t' : Fin 8 → ℤ, dotProduct s (E.mulVec t) = dotProduct s' (E.mulVec t') → ∀ p q : T,
      e (fun u => p ^ s u) (fun u => q ^ t u) = e (fun u => p ^ s' u) (fun u => q ^ t' u)) :
    ∃ b : Fin g ⊕ Fin g → T, ∀ x y : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      e (fun u => ∏ c, b c ^ x u c) (fun u => ∏ c, b c ^ y u c) = z ^ ∑ u, ∑ v, E u v * omegaStd (x u) (y v) := by
  let s₀ : Fin 8 → ℤ := Pi.single 0 1
  let t₀ : Fin 8 → ℤ := E.adjugate.mulVec s₀
  have h₀ : dotProduct s₀ (E.mulVec t₀) = 1 := by
    simp only [t₀, Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet, one_smul, Matrix.one_mulVec]
    simp [s₀]
  have h₀' : dotProduct t₀ (E.mulVec s₀) = 1 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hE, dotProduct_comm, h₀]
  let pw : (Fin 8 → ℤ) → T →* (Fin 8 → T) := fun s =>
    MonoidHom.mk' (fun p u => p ^ s u) fun p q => funext fun u => mul_zpow p q _
  let h : T →* T →* Rˣ := ((e.comp (pw s₀)).flip.comp (pw t₀)).flip
  have hh : ∀ p q, h p q = e (fun u => p ^ s₀ u) (fun u => q ^ t₀ u) := fun _ _ => rfl
  have key : ∀ (s t : Fin 8 → ℤ) (p q : T),
      e (fun u => p ^ s u) (fun u => q ^ t u) = h p q ^ dotProduct s (E.mulVec t) := fun s t p q => by
    rw [hrel s t (dotProduct s (E.mulVec t) • s₀) t₀ (by rw [smul_dotProduct, h₀, smul_eq_mul, _root_.mul_one]), hh,
      ← MonoidHom.zpow_apply, ← map_zpow]
    congr 2
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, Pi.pow_apply]
    rw [← zpow_mul, _root_.mul_comm]
  have eskew : ∀ x y, e x y * e y x = 1 := fun x y => by
    have := halt (x * y)
    simp only [map_mul, MonoidHom.mul_apply, halt, _root_.one_mul, _root_.mul_one] at this
    first | exact this | (rw [_root_.mul_comm]; exact this)
  have halt' : ∀ p, h p p = 1 := fun p => by
    have k₁ : h p p ^ 2 = 1 := by
      have := eskew (fun u => p ^ s₀ u) (fun u => p ^ t₀ u)
      rwa [key, key, h₀, h₀', zpow_one, ← pow_two] at this
    have k₂ : h p p ^ N = 1 := by rw [← map_pow, hT, map_one]
    obtain ⟨m, rfl⟩ := hN
    rwa [pow_succ, pow_mul, k₁, one_pow, _root_.one_mul] at k₂
  have hnd' : ∀ p, (∀ q, h p q = 1) → p = 1 := fun p hp => by
    have := hnd (fun u => p ^ s₀ u) fun y => by
      have hy : y = ∏ v, fun u => y v ^ (Pi.single v 1 : Fin 8 → ℤ) u := by
        funext u
        rw [Finset.prod_apply, Finset.prod_eq_single u (fun v _ hv => by simp [Pi.single_apply, hv.symm]) (by simp)]
        simp
      rw [hy, map_prod]
      exact Finset.prod_eq_one fun v _ => by rw [key, hp, one_zpow]
    simpa [s₀] using congrFun this 0
  obtain ⟨v, hv⟩ := exists_stdSymp_of_alternating_pairing N g T R z hN.pos hz hT hc h halt' hnd'
  let σ : Fin (2 * g) ≃ Fin g ⊕ Fin g := (finCongr (two_mul g)).trans finSumFinEquiv.symm
  refine ⟨fun c => v (σ.symm c), fun x y => ?_⟩
  have hp : ∀ x : Fin 8 → (Fin g ⊕ Fin g → ℤ),
      (fun u => ∏ c, v (σ.symm c) ^ x u c) = ∏ c, fun u => v (σ.symm c) ^ x u c := fun x =>
    funext fun u => by rw [Finset.prod_apply]
  rw [hp, hp]
  simp only [map_prod, MonoidHom.finset_prod_apply, key, hv, ← zpow_mul]
  have zs : ∀ {α : Type} [Fintype α] (f : α → ℤ), ∏ a, z ^ f a = z ^ ∑ a, f a := fun f =>
    (map_prod (zpowersHom Rˣ z) (fun a => Multiplicative.ofAdd (f a)) Finset.univ).symm
  simp only [zs]
  congr 1
  simp only [omegaStd_eq_sum, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u _ => ?_))
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun u' _ => ?_))
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [σ]
  ring

/- English proof (translation)
Introduce `W hW g N hN K _ _ hK z hz P hg B _ _ pr hpr hrel`. Establish `hL : Out.Laws` using `GlobalTheory.abelianSchemeLaws_all.1`. Use `P.isAb.comm` as an intermediate fact. Establish `: IsDomain Γ(Sp K, ⊤)` using `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _`. Establish `hz' : IsPrimitiveRoot (unitOn z) N` using `hz.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom) (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)`.

Take `⟨w₁, w₂, w₃, -⟩` from `hL.weil _ P N (Out.baseOver _)`. Establish `hmon` using `hpr.1`. Set `φ₀ : (Out.baseOver (Sp K) ⟶ P.A) →* (Fin 8 → (Out.baseOver (Sp K) ⟶ B))` to `MonoidHom.mk' (fun x u => x ≫ pr u) fun x y => funext fun u => MonObj.mul_comp _ _ _`. Establish `hφ : Function.Bijective φ₀` using `⟨fun x y h => (hpr.2 _ (φ₀ y)).unique (fun u => congrFun h u) fun _ => rfl, fun y => (hpr.2 _ y).exists.imp fun x hx => funext hx⟩`. Set `φ` to `MulEquiv.ofBijective φ₀ hφ`.

Establish `φa : ∀ x u, φ x u = x ≫ pr u` using `fun _ _ => rfl`. Set `T : Subgroup (Out.baseOver (Sp K) ⟶ B)` to `(powMonoidHom N).ker`. Set `ψ : (Fin 8 → T) →* (Out.baseOver (Sp K) ⟶ P.A)` to `φ.symm.toMonoidHom.comp (T.subtype.compLeft (Fin 8))`. Establish `ψa : ∀ x u, ψ x ≫ pr u = (x u).1` using `fun x u => (φa _ u).symm.trans (congrFun (φ.apply_symm_apply _) u)`. Establish `hT : ∀ x : T, x ^ N = 1` using `fun x => Subtype.ext x.2`.

Establish `ψt : ∀ x, ψ x ^ N = 1` using `fun x => by`. Rewrite using `[← map_pow, show x ^ N = 1 from funext fun u => hT _, map_one]`. Establish `ψs : ∀ y : Out.baseOver (Sp K) ⟶ P.A, y ^ N = 1 → ∃ x, ψ x = y` using `fun y hy => ⟨fun u => ⟨φ y u, by show φ y u ^ N = 1`. Rewrite using `[← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]⟩, φ.symm_apply_apply y⟩`. Use `choose w hw hw' using fun x y : Fin 8 → T => w₁ _ _ (ψt x) (ψt y)`.

Establish `wl : ∀ x x' y, w (x * x') y = w x y * w x' y` using `fun x x' y => (hw' _ _ _ (by rw [map_mul]; exact w₂ _ _ _ _ _ (hw x y) (hw x' y))).symm`. Establish `ws : ∀ x y, w y x = (w x y)⁻¹` using `fun x y => (hw' _ _ _ (CommPairing.weilIs_symm P.isLB (hw x y))).symm`. Establish `wr : ∀ x y y', w x (y * y') = w x y * w x y'` using `fun x y y' => by`. Rewrite using `[ws _ x, wl, mul_inv, ← ws, ← ws]`. Set `e : (Fin 8 → T) →* (Fin 8 → T) →* Γ(Sp K, ⊤)ˣ` to `MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x)) fun x x' => MonoidHom.ext fun y => wl x x' y`.

Establish `hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g)` using `fun d hd => by`. Establish `hA : Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g)` using `(hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd hN.pos)).2.2.2.2 K (𝟙 _) (by`. Take `⟨e, rfl⟩` from `hd`. Rewrite `hK` using `[Nat.cast_mul]`. Conclude with `left_ne_zero_of_mul hK)`.

Set `F : (Fin 8 → {x : T // x ^ d = 1}) → {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1}` to `fun x => ⟨ψ fun u => (x u).1, by`. Rewrite using `[← map_pow, show (fun u => (x u).1) ^ d = 1 from funext fun u => (x u).2, map_one]⟩`. Establish `hF : Function.Bijective F`. Use `⟨fun x y h => funext fun u => Subtype.ext (Subtype.ext ?_), fun y => ?_⟩` and prove the remaining obligations. Establish `h' : ψ (fun u => (x u).1) = ψ fun u => (y u).1` using `congrArg Subtype.val h`.

Rewrite using `[← ψa (fun u => (x u).1) u, h', ψa]`. Take `⟨x, hx⟩` from `ψs y.1 (by`. Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc, pow_mul, y.2, one_pow])`. Use `⟨fun u => ⟨x u, Subtype.ext ?_⟩, Subtype.ext hx⟩` and prove the remaining obligations.

Use `show (x u).1 ^ d = 1`. Rewrite using `[← ψa, hx, ← φa, ← Pi.pow_apply, ← map_pow, y.2, map_one, Pi.one_apply]`. Establish `h` using `Nat.card_eq_of_bijective F hF`. Rewrite `h` using `[hA, hg, Nat.card_fun, Nat.card_fin, show 2 * (8 * g) = 2 * g * 8 by ring, pow_mul]`. Conclude with `Nat.pow_left_injective (by norm_num) h`.

Take `⟨b, hb⟩` from `exists_family (g := g) hN hz' hT hc (E8Fibration.e8 W) (by simp [e8, Matrix.transpose_add, add_comm]) hW.2 e (fun x => (hw' _ _ _ (w₃ _ (ψt x))).symm) (fun x hx => by`. Establish `h1 : ψ x = 1` using `hL.weilNondeg K P N hK _ (ψt x) fun y hy => by`. Take `⟨y, rfl⟩` from `ψs y hy`. Establish `h : w x y = 1` using `hx y`. Conclude with `h ▸ hw x y`.

Use function extensionality and compare the values at `u`. Conclude with `Subtype.ext (by rw [← ψa, h1, ← φa, map_one]; rfl))`. Use the proof step `(fun s t s' t' h p q => hw' _ _ _ (hrel s t s' t' h p.1 q.1 p.2 q.2 _ _ _ _ (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) _ (hw _ _)))`. Use `⟨fun c => (b c).1, fun c => (b c).2, fun x y X Y hX hY => ?_⟩` and prove the remaining obligations. Establish `hp : ∀ (x : Fin 8 → (Fin g ⊕ Fin g → ℤ)) (X : Out.baseOver (Sp K) ⟶ P.A), (∀ u, X ≫ pr u = ∏ c, (b c).1 ^ x u c) → X = ψ fun u => ∏ c, b c ^ x u c` using `fun x X hX => hφ.1 (funext fun u => (hX u).trans (Eq.symm ((ψa _ u).trans (by simp))))`.

Rewrite using `[hp x X hX, hp y Y hY, ← hb x y]`. Conclude with `hw _ _`.
-/
theorem exists_basis : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ N : ℕ), Odd N → ∀ (K : Type) [Field K] [IsAlgClosed K], (N : K) ≠ 0 →
  ∀ (z : Kˣ), IsPrimitiveRoot z N → ∀ (P' : PolAV (Sp K)), P'.g = 8 * gQ →
  ∀ (B : Over (Sp K)) [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (P'.A ⟶ B)), E8Fibration.IsProd pr →
  (∀ (s t s' t' : Fin 8 → ℤ), dotProduct s ((E8Fibration.e8 W).mulVec t) = dotProduct s' ((E8Fibration.e8 W).mulVec t') →
    ∀ (p q : Out.baseOver (Sp K) ⟶ B), p ^ N = 1 → q ^ N = 1 →
    ∀ (x y x' y' : Out.baseOver (Sp K) ⟶ P'.A), (∀ u, x ≫ pr u = p ^ s u) → (∀ u, y ≫ pr u = q ^ t u) →
      (∀ u, x' ≫ pr u = p ^ s' u) → (∀ u, y' ≫ pr u = q ^ t' u) →
      ∀ c, Out.WeilIs P'.A P'.L N x y c → Out.WeilIs P'.A P'.L N x' y' c) →
  ∃ b : Fin gQ ⊕ Fin gQ → (Out.baseOver (Sp K) ⟶ B), (∀ c, b c ^ N = 1) ∧
    ∀ (x y : Fin 8 → (Fin gQ ⊕ Fin gQ → ℤ)) (X Y : Out.baseOver (Sp K) ⟶ P'.A),
      (∀ u, X ≫ pr u = ∏ c, b c ^ x u c) → (∀ u, Y ≫ pr u = ∏ c, b c ^ y u c) →
      Out.WeilIs P'.A P'.L N X Y (unitOn z ^ ∑ u, ∑ v, E8Fibration.e8 W u v * omegaStd (x u) (y v)) := by
  intro W hW g N hN K _ _ hK z hz P hg B _ _ pr hpr hrel
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have : IsDomain Γ(Sp K, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  have hz' : IsPrimitiveRoot (unitOn z) N :=
    hz.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).1)
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P N (Out.baseOver _)
  have hmon := hpr.1
  let φ₀ : (Out.baseOver (Sp K) ⟶ P.A) →* (Fin 8 → (Out.baseOver (Sp K) ⟶ B)) :=
    MonoidHom.mk' (fun x u => x ≫ pr u) fun x y => funext fun u => MonObj.mul_comp _ _ _
  have hφ : Function.Bijective φ₀ :=
    ⟨fun x y h => (hpr.2 _ (φ₀ y)).unique (fun u => congrFun h u) fun _ => rfl,
      fun y => (hpr.2 _ y).exists.imp fun x hx => funext hx⟩
  let φ := MulEquiv.ofBijective φ₀ hφ
  have φa : ∀ x u, φ x u = x ≫ pr u := fun _ _ => rfl
  let T : Subgroup (Out.baseOver (Sp K) ⟶ B) := (powMonoidHom N).ker
  let ψ : (Fin 8 → T) →* (Out.baseOver (Sp K) ⟶ P.A) :=
    φ.symm.toMonoidHom.comp (T.subtype.compLeft (Fin 8))
  have ψa : ∀ x u, ψ x ≫ pr u = (x u).1 := fun x u =>
    (φa _ u).symm.trans (congrFun (φ.apply_symm_apply _) u)
  have hT : ∀ x : T, x ^ N = 1 := fun x => Subtype.ext x.2
  have ψt : ∀ x, ψ x ^ N = 1 := fun x => by
    rw [← map_pow, show x ^ N = 1 from funext fun u => hT _, map_one]
  have ψs : ∀ y : Out.baseOver (Sp K) ⟶ P.A, y ^ N = 1 → ∃ x, ψ x = y := fun y hy =>
    ⟨fun u => ⟨φ y u, by
      show φ y u ^ N = 1
      rw [← Pi.pow_apply, ← map_pow, hy, map_one, Pi.one_apply]⟩, φ.symm_apply_apply y⟩
  choose w hw hw' using fun x y : Fin 8 → T => w₁ _ _ (ψt x) (ψt y)
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (by rw [map_mul]; exact w₂ _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (CommPairing.weilIs_symm P.isLB (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : (Fin 8 → T) →* (Fin 8 → T) →* Γ(Sp K, ⊤)ˣ := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  have hc : ∀ d : ℕ, d ∣ N → Nat.card {x : T // x ^ d = 1} = d ^ (2 * g) := fun d hd => by
    have hA : Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) :=
      (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd hN.pos)).2.2.2.2 K (𝟙 _) (by
        obtain ⟨e, rfl⟩ := hd
        rw [Nat.cast_mul] at hK
        exact left_ne_zero_of_mul hK)
    let F : (Fin 8 → {x : T // x ^ d = 1}) → {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} := fun x =>
      ⟨ψ fun u => (x u).1, by
        rw [← map_pow, show (fun u => (x u).1) ^ d = 1 from funext fun u => (x u).2, map_one]⟩
    have hF : Function.Bijective F := by
      refine ⟨fun x y h => funext fun u => Subtype.ext (Subtype.ext ?_), fun y => ?_⟩
      · have h' : ψ (fun u => (x u).1) = ψ fun u => (y u).1 := congrArg Subtype.val h
        rw [← ψa (fun u => (x u).1) u, h', ψa]
      · obtain ⟨x, hx⟩ := ψs y.1 (by
          obtain ⟨c, hc⟩ := hd
          rw [hc, pow_mul, y.2, one_pow])
        refine ⟨fun u => ⟨x u, Subtype.ext ?_⟩, Subtype.ext hx⟩
        show (x u).1 ^ d = 1
        rw [← ψa, hx, ← φa, ← Pi.pow_apply, ← map_pow, y.2, map_one, Pi.one_apply]
    have h := Nat.card_eq_of_bijective F hF
    rw [hA, hg, Nat.card_fun, Nat.card_fin, show 2 * (8 * g) = 2 * g * 8 by ring, pow_mul] at h
    exact Nat.pow_left_injective (by norm_num) h
  obtain ⟨b, hb⟩ := exists_family (g := g) hN hz' hT hc (E8Fibration.e8 W)
    (by simp [e8, Matrix.transpose_add, add_comm]) hW.2 e
    (fun x => (hw' _ _ _ (w₃ _ (ψt x))).symm)
    (fun x hx => by
      have h1 : ψ x = 1 := hL.weilNondeg K P N hK _ (ψt x) fun y hy => by
        obtain ⟨y, rfl⟩ := ψs y hy
        have h : w x y = 1 := hx y
        exact h ▸ hw x y
      funext u
      exact Subtype.ext (by rw [← ψa, h1, ← φa, map_one]; rfl))
    (fun s t s' t' h p q => hw' _ _ _ (hrel s t s' t' h p.1 q.1 p.2 q.2 _ _ _ _
      (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) (fun u => ψa _ u) _ (hw _ _)))
  refine ⟨fun c => (b c).1, fun c => (b c).2, fun x y X Y hX hY => ?_⟩
  have hp : ∀ (x : Fin 8 → (Fin g ⊕ Fin g → ℤ)) (X : Out.baseOver (Sp K) ⟶ P.A),
      (∀ u, X ≫ pr u = ∏ c, (b c).1 ^ x u c) → X = ψ fun u => ∏ c, b c ^ x u c := fun x X hX =>
    hφ.1 (funext fun u => (hX u).trans (Eq.symm ((ψa _ u).trans (by simp))))
  rw [hp x X hX, hp y Y hY, ← hb x y]
  exact hw _ _

end GlobalTheory.Poinc.Sep.E8Fibration.FactorBasis
