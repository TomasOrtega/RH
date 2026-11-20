import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CuspSemisimpleReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.RepNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Af.Nf

/- English proof (translation)
Introduce `k M hM χ ω hω f hf`. Take `⟨φ₀, hφ⟩` from `liftEx k M hM f fun δ hδ => SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩`. Take `⟨hl, hr, hs⟩` from `liftSm k M hM f φ₀ hφ`. Set `φ : TR.Sm ℚ 2` to `⟨φ₀, hs f.holo'⟩`. Establish `hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ` using `fun u hu => Subtype.ext (funext (hr u hu))`.

Establish `hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ}` using `isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)`. Establish `hc` using `liftCent k M hM χ ω hω f hf φ₀ hφ`. Establish `hlie` using `liftLie k M hM f f.holo' φ hφ`. Take `⟨C, hC⟩` from `archBd k M hM f`. Establish `haut : TR.IsAutForm φ` using `⟨hl, hlev, liftK k M hM f φ hφ, zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2), fun g => ⟨C, 0, fun y => by`.

Take `⟨γ, h, u, hu, e⟩` from `decomp M hM (g * TR.infGL ℚ 2 y)`. Rewrite using `[pow_zero, mul_one, e]`. Express the relevant statement in the definitionally equal form `‖φ₀ _‖ ≤ C`. Rewrite using `[hφ γ h u hu]`. Conclude with `hC _ h.det_ne_zero⟩⟩`.

Conclude with `⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc, fun v => (hlie v).1, fun v => (hlie v).2⟩, haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩`.
-/
private theorem liftHol : LiftHol := by
  intro k M hM χ ω hω f hf
  obtain ⟨φ₀, hφ⟩ := liftEx k M hM f fun δ hδ => SlashInvariantForm.slash_action_eqn f δ ⟨δ, hδ, rfl⟩
  obtain ⟨hl, hr, hs⟩ := liftSm k M hM f φ₀ hφ
  let φ : TR.Sm ℚ 2 := ⟨φ₀, hs f.holo'⟩
  have hfix : ∀ u ∈ K1G M, TR.finRep ℚ 2 u φ = φ := fun u hu => Subtype.ext (funext (hr u hu))
  have hlev : IsOpen {u | TR.finRep ℚ 2 u φ = φ} :=
    isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset ((kOpen M hM).1.mem_nhds (one_mem _)) hfix)
  have hc := liftCent k M hM χ ω hω f hf φ₀ hφ
  have hlie := liftLie k M hM f f.holo' φ hφ
  obtain ⟨C, hC⟩ := archBd k M hM f
  have haut : TR.IsAutForm φ := ⟨hl, hlev, liftK k M hM f φ hφ,
    zFin ℚ k ω (charVal M hM χ ω hω).1 φ hc (fun v => (hlie v).1) (fun v => (hlie v).2), fun g => ⟨C, 0, fun y => by
      obtain ⟨γ, h, u, hu, e⟩ := decomp M hM (g * TR.infGL ℚ 2 y)
      rw [pow_zero, mul_one, e]
      change ‖φ₀ _‖ ≤ C
      rw [hφ γ h u hu]
      exact hC _ h.det_ne_zero⟩⟩
  exact ⟨φ, hφ, ⟨haut, fun w u hu => hfix _ (kLocal M hM w u hu), hc, fun v => (hlie v).1, fun v => (hlie v).2⟩,
    haut, cuspCrit φ hl hlev (liftCT k M hM f φ₀ hφ)⟩

/- English proof (translation)
Introduce `F _ _ _ k hk1 c ω hω φ hφ h0 hcusp j`. Take `⟨h1, hcap⟩` from `holCap F k c ω hω φ hφ`. Take `⟨π, ψ, W, hψ, hW, hd, hm⟩` from `split F 2 φ h0 (hS F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)`. Use `set s : ℝ := 1 - (k : ℝ) / 2 + j with hs`. Set `χ` to `GlobalTheory.HeckeGal.Model.absPow F s`.

Establish `hE` using `GlobalTheory.HeckeGal.Model.absPow_isAbsPow F s`. Use `⟨π.twist χ, fun v => ?_, fun w lam hc he => ?_⟩` and prove the remaining obligations. Establish `hi : π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)}`. Use `⟨rfl, fun u x hx => ?_⟩` and prove the remaining obligations. Take `⟨d, hd'⟩` from `TR.Cen.exists_cap_scalar π`.

Establish `h2 : TR.cap v u (φ - ψ.1) ∈ W` using `TR.Zalg_stable (fun X => hW (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩) _ hm`. Use `set t := (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)`. Establish `h3 : (t - d v u) • ψ.1 ∈ W`. Use `W.sub_mem h2 (W.smul_mem t hm)` as an intermediate fact. Rewrite `this` using `[map_sub, hcap v u, hd' v u ψ ψ.2]`.

Use `this using 1` and compare the differences between its conclusion and the goal. Use `module`. Establish `h4` using `(Submodule.disjoint_def.1 hd) _ (π.V.smul_mem _ ψ.2) h3`. Establish `h5 : t = d v u` using `sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right fun e => hψ (Subtype.ext e))`. Rewrite using `[hd' v u x hx, ← h5]`.

Simplify using `[t, sub_eq_add_neg]`. Use `hi.twist χ` as an intermediate fact. Rewrite `this` using `[absExpo F s v]`. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]`.

Conclude with `congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)`. Take `⟨α, β, hv, hsum, hprod⟩` from `satHol F k c ω φ hφ h0 w lam hc he`. Use `⟨_, (satOfVec hA F 2 π w ψ _ (satComp F φ π ψ W hψ hW hd hm w _ hv)).twist (χ := χ) (hE.1 w), ?_⟩` and prove the remaining obligations. Establish `hq : Ideal.absNorm w.asIdeal = normV w` using `by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl`. Establish `hq0 : (0 : ℝ) < normV w`.

Rewrite using `[← hq]; exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)`. Establish `hval : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ)`. Rewrite using `[hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]`. Simplify using the standard rewrite rules. Use `set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr`.

Establish `key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * χ.val w : ℂˣ) : ℂ)) = r * a` using `fun a => by`. Establish `: ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) = (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s))`. Rewrite using `[← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]`. Use `congr 1`. Rewrite using `[hs]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hr, this, Units.val_mul, hval]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hrr : r * r = (normV w : ℂ) ^ (k - 1)`. Rewrite using `[hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons, Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind, Multiset.singleton_add, key]`.

Rewrite using `[← hsum, ← hprod, ← hrr]`. Simplify using `only [Units.val_mul, C_mul, C_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem repOf (hS : Published.CuspSemisimpleReal) (hA : Published.AdmissibleReal) : RepOf := by
  intro F _ _ _ k hk1 c ω hω φ hφ h0 hcusp j
  obtain ⟨h1, hcap⟩ := holCap F k c ω hω φ hφ
  obtain ⟨π, ψ, W, hψ, hW, hd, hm⟩ := split F 2 φ h0 (hS F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set s : ℝ := 1 - (k : ℝ) / 2 + j with hs
  let χ := GlobalTheory.HeckeGal.Model.absPow F s
  have hE := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F s
  refine ⟨π.twist χ, fun v => ?_, fun w lam hc he => ?_⟩
  · have hi : π.HasInfChar v {((k : ℂ) - 1) / 2, -(((k : ℂ) - 1) / 2)} := by
      refine ⟨rfl, fun u x hx => ?_⟩
      obtain ⟨d, hd'⟩ := TR.Cen.exists_cap_scalar π
      have h2 : TR.cap v u (φ - ψ.1) ∈ W := TR.Zalg_stable (fun X => hW (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩) _ hm
      set t := (u + ((k : ℂ) - 1) / 2) * (u - ((k : ℂ) - 1) / 2)
      have h3 : (t - d v u) • ψ.1 ∈ W := by
        have := W.sub_mem h2 (W.smul_mem t hm)
        rw [map_sub, hcap v u, hd' v u ψ ψ.2] at this
        convert this using 1
        module
      have h4 := (Submodule.disjoint_def.1 hd) _ (π.V.smul_mem _ ψ.2) h3
      have h5 : t = d v u := sub_eq_zero.1 ((smul_eq_zero.1 h4).resolve_right fun e => hψ (Subtype.ext e))
      rw [hd' v u x hx, ← h5]
      simp [t, sub_eq_add_neg]
    have := hi.twist χ
    rw [absExpo F s v] at this
    convert this using 1
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, hs]
    exact congrArg₂ (fun a b : ℂ => a ::ₘ {b}) (by push_cast; ring) (by push_cast; ring)
  · obtain ⟨α, β, hv, hsum, hprod⟩ := satHol F k c ω φ hφ h0 w lam hc he
    refine ⟨_, (satOfVec hA F 2 π w ψ _ (satComp F φ π ψ W hψ hW hd hm w _ hv)).twist (χ := χ) (hE.1 w), ?_⟩
    have hq : Ideal.absNorm w.asIdeal = normV w := by rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
    have hq0 : (0 : ℝ) < normV w := by
      rw [← hq]; exact_mod_cast Nat.pos_of_ne_zero (by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot)
    have hval : ((χ.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ (-s) : ℝ) : ℂ) := by
      rw [hE.2.1 w, hq, Complex.ofReal_cpow hq0.le]; simp
    set r : ℂ := (((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) : ℂ) with hr
    have key : ∀ a : ℂˣ, (normV w : ℂ) ^ j * ((((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) : ℝ) : ℂ) * ((a * χ.val w : ℂˣ) : ℂ)) =
        r * a := fun a => by
      have : ((normV w : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ) =
          (normV w : ℝ) ^ j * ((normV w : ℝ) ^ ((((2 : ℕ) : ℝ) - 1) / 2) * (normV w : ℝ) ^ (-s)) := by
        rw [← Real.rpow_intCast, ← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 1
        rw [hs]; push_cast; ring
      rw [hr, this, Units.val_mul, hval]; push_cast; ring
    have hrr : r * r = (normV w : ℂ) ^ (k - 1) := by
      rw [hr, ← Complex.ofReal_mul, ← Real.rpow_add hq0, add_halves, ← Nat.cast_pred hk1, Real.rpow_natCast]
      push_cast; rfl
    simp only [algSat, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, Multiset.pure_def, Multiset.bind_def, Multiset.cons_bind, Multiset.singleton_bind,
      Multiset.singleton_add, key]
    rw [← hsum, ← hprod, ← hrr]
    simp only [Units.val_mul, C_mul, C_add]
    ring

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
/- English proof (translation)
Introduce `hS hA k hk2 f j`. Establish `hM : 1 ≤ f.M` using `f.pos`. Establish `hk1 : 1 ≤ k` using `by omega`. Take `⟨ω, hω⟩` from `dirChar f.M hM f.χ`. Take `⟨hfin, hval⟩` from `charVal f.M hM f.χ ω hω`.

Take `⟨φ, hL, hH, hC⟩` from `liftHol k f.M hM f.χ ω hω f.f f.char`. Establish `hE` using `liftExp k f.M hM f.f φ.1 hL`. Take `⟨-, hz, hl1, hl2, -⟩` from `holLin ℚ k (lev f.M) ω`. Establish `h0 : φ ≠ 0`. Introduce and unpack `rfl`.

Use `(expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot` as an intermediate fact. Rewrite `this` using `[icoef, Ideal.absNorm_top, f.one]`. Conclude with `one_ne_zero this`. Take `⟨π, hi, hs⟩` from `repOf hS hA ℚ k hk1 _ ω hfin φ hH h0 hC j`. Use `⟨π, hi, fun w hw => ?_⟩` and prove the remaining obligations.

Establish `hc` using `(places w).2.2.2 f.M hM hw`. Take `⟨h1, -, h2⟩` from `holHk ℚ k hk1 _ ω hfin φ hH w`. Take `⟨c₀, h3⟩` from `h2 _ _ hE`. Establish `h4` using `expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE) fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]`. Rewrite `h4` using `[hc, neg_smul, add_neg_eq_zero]`.

Take `⟨B, hB, e⟩` from `hs w _ hc h4`. Conclude with `⟨B, hB, by rw [e, hval w hw, Newform.heckePoly]⟩`.
-/
theorem UpperTheory.V.Af.newformRepOf :
    UpperTheory.V.Published.CuspSemisimpleReal → UpperTheory.V.Published.AdmissibleReal → UpperTheory.V.Published.NewformRep := by
  intro hS hA k hk2 f j
  have hM : 1 ≤ f.M := f.pos
  have hk1 : 1 ≤ k := by omega
  obtain ⟨ω, hω⟩ := dirChar f.M hM f.χ
  obtain ⟨hfin, hval⟩ := charVal f.M hM f.χ ω hω
  obtain ⟨φ, hL, hH, hC⟩ := liftHol k f.M hM f.χ ω hω f.f f.char
  have hE := liftExp k f.M hM f.f φ.1 hL
  obtain ⟨-, hz, hl1, hl2, -⟩ := holLin ℚ k (lev f.M) ω
  have h0 : φ ≠ 0 := by
    rintro rfl
    have := (expUnique ℚ _ k _ _ _ _ hE hz).2 ⊤ top_ne_bot
    rw [icoef, Ideal.absNorm_top, f.one] at this
    exact one_ne_zero this
  obtain ⟨π, hi, hs⟩ := repOf hS hA ℚ k hk1 _ ω hfin φ hH h0 hC j
  refine ⟨π, hi, fun w hw => ?_⟩
  have hc := (places w).2.2.2 f.M hM hw
  obtain ⟨h1, -, h2⟩ := holHk ℚ k hk1 _ ω hfin φ hH w
  obtain ⟨c₀, h3⟩ := h2 _ _ hE
  have h4 := expInj ℚ k hk1 _ ω hfin _ (hl1 _ _ (-f.a (normV w)) h1 hH) _ _ (hl2 _ _ (-f.a (normV w)) _ _ _ _ h3 hE)
    fun 𝔪 h𝔪 => by simp [hkCoef k f ω w hw (hval w hw) 𝔪 h𝔪]
  rw [hc, neg_smul, add_neg_eq_zero] at h4
  obtain ⟨B, hB, e⟩ := hs w _ hc h4
  exact ⟨B, hB, by rw [e, hval w hw, Newform.heckePoly]⟩
