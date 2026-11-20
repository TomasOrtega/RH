import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumProdFixedPlaceAverageStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.LabFix

section Gen

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show f (g * (a * b)) = f (g * a * b)`. Rewrite using `[mul_assoc]`.
-/
theorem rt_mul (a b : GAf L n) (f : GAf L n → ℂ) :
    Formalism.L2.NG.rt L n (a * b) f = Formalism.L2.NG.rt L n a (Formalism.L2.NG.rt L n b f) := by
  funext g
  show f (g * (a * b)) = f (g * a * b)
  rw [mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `show f (g * 1) = f g`. Rewrite using `[mul_one]`.
-/
theorem rt_one (f : GAf L n → ℂ) : Formalism.L2.NG.rt L n 1 f = f := by
  funext g
  show f (g * 1) = f g
  rw [mul_one]

/- English proof (translation)
Use `haveI : Fact g.Prime := ⟨hg⟩`. Establish `key : ∀ γ : GL (Fin n) (ZMod g), ∃ x : GAf L n, IsLift s x γ`. Introduce `γ`. Set `A : Matrix (Fin n) (Fin n) ℤ` to `fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)`. Establish `hA : (Int.castRingHom (ZMod g)).mapMatrix A = (γ : Matrix (Fin n) (Fin n) (ZMod g))`.

Use extensionality with `i j`. Use `show ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ) : ZMod g) = _`. Rewrite using `[Int.cast_natCast, ZMod.natCast_zmod_val]`. Establish `hdet : A.det ≠ 0`. Introduce `h0`.

Establish `h1` using `congrArg (Int.castRingHom (ZMod g)) h0`. Rewrite `h1` using `[RingHom.map_det, hA, map_zero]`. Conclude with `(Matrix.isUnits_det_units γ).ne_zero h1`. Set `B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))` to `(Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))).mapMatrix A`. Establish `hB : IsUnit B.det`.

Rewrite using `[isUnit_iff_ne_zero, ← RingHom.map_det, eq_intCast]`. Conclude with `Int.cast_ne_zero.mpr hdet`. Take `⟨x, hx, hloc⟩` from `GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq n s (Matrix.nonsingInvUnit B hB)`. Use `⟨x, hx, fun i j => ?_⟩` and prove the remaining obligations. Establish `hij : (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j = ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L))`.

Rewrite using `[hloc]`. Use `show (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) (A i j) = _`. Rewrite using `[eq_intCast]`. Conclude with `Int.cast_natCast _`. Rewrite using `[hij, sub_self, map_zero]`.

Conclude with `zero_lt_one`. Use `choose ℓ hℓ using key`. Conclude with `⟨ℓ, hℓ⟩`.
-/
theorem exists_lifts (n : ℕ) (s : SplitPlace L) (g : ℕ) (hg : g.Prime) :
    ∃ ℓ : GL (Fin n) (ZMod g) → GAf L n, ∀ γ, IsLift s (ℓ γ) γ := by
  classical
  haveI : Fact g.Prime := ⟨hg⟩
  have key : ∀ γ : GL (Fin n) (ZMod g), ∃ x : GAf L n, IsLift s x γ := by
    intro γ
    let A : Matrix (Fin n) (Fin n) ℤ := fun i j => (((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ)
    have hA : (Int.castRingHom (ZMod g)).mapMatrix A = (γ : Matrix (Fin n) (Fin n) (ZMod g)) := by
      ext i j
      show ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℤ) : ZMod g) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have hdet : A.det ≠ 0 := by
      intro h0
      have h1 := congrArg (Int.castRingHom (ZMod g)) h0
      rw [RingHom.map_det, hA, map_zero] at h1
      exact (Matrix.isUnits_det_units γ).ne_zero h1
    let B : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L)) :=
      (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))).mapMatrix A
    have hB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero, ← RingHom.map_det, eq_intCast]
      exact Int.cast_ne_zero.mpr hdet
    obtain ⟨x, hx, hloc⟩ := GlobalTheory.T.exists_adelicUnitary_trivialOutside_splitPlace_loc_eq n s (Matrix.nonsingInvUnit B hB)
    refine ⟨x, hx, fun i j => ?_⟩
    have hij : (s.loc n x : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j =
        ((((γ : Matrix (Fin n) (Fin n) (ZMod g)) i j).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) := by
      rw [hloc]
      show (Int.castRingHom (s.v.adicCompletion (maximalRealSubfield L))) (A i j) = _
      rw [eq_intCast]
      exact Int.cast_natCast _
    rw [hij, sub_self, map_zero]
    exact zero_lt_one
  choose ℓ hℓ using key
  exact ⟨ℓ, hℓ⟩

end Gen

/- English proof (translation)
Introduce `D X h t PY c red sec lf hFR hsec hlf π τ hτ φ hφ hfix`. Take `⟨hred, hex, hlift⟩` from `hFR`. Take `⟨-, hmul, -, hker⟩` from `hred`. Use `haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Establish `kap_mul : ∀ k k' : X.B.I.Gf, kap X h t (k * k') = kap X h t k * kap X h t k'`.

Introduce `k k'`. Establish `e : ((1, k * k') : X.B.I.GA) = (1, k) * (1, k')` using `by rw [Prod.mk_mul_mk, one_mul]`. Establish `cm : ∀ a b : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t)`. Introduce `a b`. Use `group`.

Unfold `kap`. Rewrite using `[e, map_mul]`. Conclude with `cm _ _`. Establish `kap_inv : ∀ k : X.B.I.Gf, kap X h t k⁻¹ = (kap X h t k)⁻¹`. Introduce `k`.

Establish `e : ((1, k⁻¹) : X.B.I.GA) = (1, k)⁻¹` using `by rw [Prod.inv_mk, inv_one]`. Establish `ci : ∀ a : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹`. Introduce `a`. Use `group`. Unfold `kap`.

Rewrite using `[e, map_inv]`. Conclude with `ci _`. Establish `K_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset`. Simplify using `only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, OneMemClass.coe_one]`. Conclude with `one_mem _`.

Establish `K_mul : ∀ a b : X.B.I.Gf, a ∈ X.B.I.Kset → b ∈ X.B.I.Kset → a * b ∈ X.B.I.Kset`. Introduce `a b ha hb`. Simplify using `only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at *`. Conclude with `mul_mem ha hb`. Establish `K_inv : ∀ a : X.B.I.Gf, a ∈ X.B.I.Kset → a⁻¹ ∈ X.B.I.Kset`.

Introduce `a ha`. Simplify using `only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, InvMemClass.coe_inv] at *`. Conclude with `inv_mem ha`. Establish `red_one : red 1 = 1`. Establish `e` using `hmul 1 K_one 1 K_one`.

Rewrite `e` using `[one_mul]`. Conclude with `mul_left_cancel (e.symm.trans (mul_one _).symm)`. Establish `red_inv : ∀ k ∈ X.B.I.Kset, red k⁻¹ = (red k)⁻¹`. Introduce `k hk`. Establish `e` using `hmul k⁻¹ (K_inv k hk) k hk`.

Rewrite `e` using `[inv_mul_cancel, red_one]`. Conclude with `eq_inv_of_mul_eq_one_left e.symm`. Establish `key : ∀ (γ : G0g D.nd) (y : GAf D.host.E D.R.r) (k : X.B.I.Gf), k ∈ X.B.I.Kset → red k = γ → PY.ψ y = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r y φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ`. Introduce `γ y k hk hrk hy`. Take `⟨hs1, hs2⟩` from `hsec γ`.

Establish `hm : (sec γ)⁻¹ * k ∈ X.B.I.Kg X.B.g`. Use `(hker _ (K_mul _ _ (K_inv _ hs1) hk)).1 ?_` and prove the remaining obligations. Rewrite using `[hmul _ (K_inv _ hs1) _ hk, red_inv _ hs1, hs2, hrk, inv_mul_cancel]`. Establish `hψ : PY.ψ ((lf γ)⁻¹ * y) = kap X h t ((sec γ)⁻¹ * k)`. Rewrite using `[map_mul, map_inv, hlf, hy, kap_mul, kap_inv]`.

Establish `e` using `hfix _ hm _ hψ`. Combine the equalities or inequalities in the displayed calculation. Use `set φ' := Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ φ with hφ'`. Establish `hφ'S : φ' ∈ π.S` using `π.stable _ _ hφ`. Establish `back : Formalism.L2.NG.rt D.host.E D.R.r c φ' = φ`.

Rewrite using `[hφ', ← rt_mul, mul_inv_cancel, rt_one]`. Establish `fix1 : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 → ∀ x, IsLift s x (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) → Formalism.L2.NG.rt D.host.E D.R.r x φ' = φ'`. Introduce `kv s hs x hx`. Take `⟨k, hk, hψ, hr1, hr2⟩` from `hlift kv s hs x 1 hx`. Establish `hrk : red k = 1`.

Use function extensionality and compare the values at `kv'`. Rewrite using `[Pi.one_apply]`. Distinguish the cases in `e : kv' = kv`. Substitute `e` using the available equality. Conclude with `hr1`.

Conclude with `hr2 kv' e`. Establish `e` using `hfix k ((hker k hk).1 hrk) _ hψ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hφ', ← rt_mul, ← rt_mul]`. Use `congr 1`.

Use `group`. Use `_ = φ' := by rw [e]`. Establish `step : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (γ : G0g D.nd), γ kv = 1 → ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β • Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ`. Introduce `kv γ hγ`. Take `⟨s, hs⟩` from `hex kv`.

Take `⟨ℓ, hℓ⟩` from `exists_lifts D.R.r s (D.host.g kv.1) (D.host.g_prime kv.1)`. Establish `hser` using `((hτ kv.1 kv.2).2 s hs) ℓ hℓ φ' hφ'S (fix1 kv s hs)`. Rewrite `hser` using `[finsum_eq_sum_of_fintype]`. Establish `hterm : ∀ β, Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ'))`. Introduce `β`.

Take `⟨k, hk, hψ, hr1, hr2⟩` from `hlift kv s hs (ℓ β) β (hℓ β)`. Take `⟨hs1, hs2⟩` from `hsec γ`. Establish `hred : red (sec γ * k) = Function.update γ kv β`. Rewrite using `[hmul _ hs1 _ hk, hs2]`. Use function extensionality and compare the values at `kv'`.

Distinguish the cases in `e : kv' = kv`. Substitute `e` using the available equality. Simplify using `[hγ, hr1]`. Simplify using `[Function.update_of_ne e, hr2 kv' e]`. Establish `e` using `key _ (lf γ * (c * ℓ β * c⁻¹)) (sec γ * k) (K_mul _ _ hs1 hk) hred (by rw [map_mul, hlf, hψ, kap_mul])`.

Rewrite using `[← e, hφ', ← rt_mul, ← rt_mul, ← rt_mul]`. Use `congr 1`. Use `group`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_smul]`.

Use `_ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [hser, back]`. Establish `hfin` using `GlobalTheory.T.sum_prod_fixed_place_average_alt (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) (fun kv β => (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β) (fun γ => Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ) step`. Establish `h1 : Formalism.L2.NG.rt D.host.E D.R.r (lf 1) φ = φ` using `hfix (sec 1) ((hker _ (hsec 1).1).1 ((hsec 1).2)) _ (hlf 1)`. Rewrite using `[finsum_eq_sum_of_fintype]`. Conclude with `hfin.trans h1`.
-/
theorem sum_serCoef_rt : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : Formalism.L2.Theta.GA D (D.sp.Y 0)) (PY : RowPsi (Yc D 0) D.R.r) (c : GAf D.host.E D.R.r) (red : X.B.I.Gf → G0g D.nd) (sec : G0g D.nd → X.B.I.Gf) (lf : G0g D.nd → GAf D.host.E D.R.r), FrameRed X h t PY c red → IsSec X red sec → (∀ γ, PY.ψ (lf γ) = kap X h t (sec γ)) → ∀ (π : Formalism.L2.NG.FinTyp D.host.E D.R.r) (τ : Tup2 D), HasTuple D π τ → ∀ φ ∈ π.S, (∀ k ∈ X.B.I.Kg X.B.g, ∀ κ, PY.ψ κ = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r κ φ = φ) → ∑ᶠ γ, serCoef τ γ • Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ = φ := by
  intro D X h t PY c red sec lf hFR hsec hlf π τ hτ φ hφ hfix
  classical
  obtain ⟨hred, hex, hlift⟩ := hFR
  obtain ⟨-, hmul, -, hker⟩ := hred
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have kap_mul : ∀ k k' : X.B.I.Gf, kap X h t (k * k') = kap X h t k * kap X h t k' := by
    intro k k'
    have e : ((1, k * k') : X.B.I.GA) = (1, k) * (1, k') := by rw [Prod.mk_mul_mk, one_mul]
    have cm : ∀ a b : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t) := by
      intro a b; group
    unfold kap
    rw [e, map_mul]
    exact cm _ _
  have kap_inv : ∀ k : X.B.I.Gf, kap X h t k⁻¹ = (kap X h t k)⁻¹ := by
    intro k
    have e : ((1, k⁻¹) : X.B.I.GA) = (1, k)⁻¹ := by rw [Prod.inv_mk, inv_one]
    have ci : ∀ a : Formalism.L2.Theta.GA D (D.sp.Y 0), t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by
      intro a; group
    unfold kap
    rw [e, map_inv]
    exact ci _
  have K_one : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, OneMemClass.coe_one]
    exact one_mem _
  have K_mul : ∀ a b : X.B.I.Gf, a ∈ X.B.I.Kset → b ∈ X.B.I.Kset → a * b ∈ X.B.I.Kset := by
    intro a b ha hb
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, Subgroup.coe_mul] at *
    exact mul_mem ha hb
  have K_inv : ∀ a : X.B.I.Gf, a ∈ X.B.I.Kset → a⁻¹ ∈ X.B.I.Kset := by
    intro a ha
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq, InvMemClass.coe_inv] at *
    exact inv_mem ha
  have red_one : red 1 = 1 := by
    have e := hmul 1 K_one 1 K_one
    rw [one_mul] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have red_inv : ∀ k ∈ X.B.I.Kset, red k⁻¹ = (red k)⁻¹ := by
    intro k hk
    have e := hmul k⁻¹ (K_inv k hk) k hk
    rw [inv_mul_cancel, red_one] at e
    exact eq_inv_of_mul_eq_one_left e.symm
  have key : ∀ (γ : G0g D.nd) (y : GAf D.host.E D.R.r) (k : X.B.I.Gf), k ∈ X.B.I.Kset → red k = γ →
      PY.ψ y = kap X h t k → Formalism.L2.NG.rt D.host.E D.R.r y φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro γ y k hk hrk hy
    obtain ⟨hs1, hs2⟩ := hsec γ
    have hm : (sec γ)⁻¹ * k ∈ X.B.I.Kg X.B.g := by
      refine (hker _ (K_mul _ _ (K_inv _ hs1) hk)).1 ?_
      rw [hmul _ (K_inv _ hs1) _ hk, red_inv _ hs1, hs2, hrk, inv_mul_cancel]
    have hψ : PY.ψ ((lf γ)⁻¹ * y) = kap X h t ((sec γ)⁻¹ * k) := by
      rw [map_mul, map_inv, hlf, hy, kap_mul, kap_inv]
    have e := hfix _ hm _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r y φ
        = Formalism.L2.NG.rt D.host.E D.R.r (lf γ * ((lf γ)⁻¹ * y)) φ := by rw [mul_inv_cancel_left]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r ((lf γ)⁻¹ * y) φ) := rt_mul _ _ _
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [e]
  set φ' := Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ φ with hφ'
  have hφ'S : φ' ∈ π.S := π.stable _ _ hφ
  have back : Formalism.L2.NG.rt D.host.E D.R.r c φ' = φ := by
    rw [hφ', ← rt_mul, mul_inv_cancel, rt_one]
  have fix1 : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (s : SplitPlace D.host.E), s.w = D.naut.plGw kv.1 kv.2 →
      ∀ x, IsLift s x (1 : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) → Formalism.L2.NG.rt D.host.E D.R.r x φ' = φ' := by
    intro kv s hs x hx
    obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs x 1 hx
    have hrk : red k = 1 := by
      funext kv'
      rw [Pi.one_apply]
      by_cases e : kv' = kv
      · subst e; exact hr1
      · exact hr2 kv' e
    have e := hfix k ((hker k hk).1 hrk) _ hψ
    calc Formalism.L2.NG.rt D.host.E D.R.r x φ'
        = Formalism.L2.NG.rt D.host.E D.R.r c⁻¹ (Formalism.L2.NG.rt D.host.E D.R.r (c * x * c⁻¹) φ) := by
          rw [hφ', ← rt_mul, ← rt_mul]; congr 1; group
      _ = φ' := by rw [e]
  have step : ∀ (kv : (Σ k : Fin 2, D.nd.PlG k)) (γ : G0g D.nd), γ kv = 1 →
      ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
        Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by
    intro kv γ hγ
    obtain ⟨s, hs⟩ := hex kv
    obtain ⟨ℓ, hℓ⟩ := exists_lifts D.R.r s (D.host.g kv.1) (D.host.g_prime kv.1)
    have hser := ((hτ kv.1 kv.2).2 s hs) ℓ hℓ φ' hφ'S (fix1 kv s hs)
    rw [finsum_eq_sum_of_fintype] at hser
    have hterm : ∀ β, Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ =
        Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
      intro β
      obtain ⟨k, hk, hψ, hr1, hr2⟩ := hlift kv s hs (ℓ β) β (hℓ β)
      obtain ⟨hs1, hs2⟩ := hsec γ
      have hred : red (sec γ * k) = Function.update γ kv β := by
        rw [hmul _ hs1 _ hk, hs2]
        funext kv'
        by_cases e : kv' = kv
        · subst e; simp [hγ, hr1]
        · simp [Function.update_of_ne e, hr2 kv' e]
      have e := key _ (lf γ * (c * ℓ β * c⁻¹)) (sec γ * k) (K_mul _ _ hs1 hk) hred
        (by rw [map_mul, hlf, hψ, kap_mul])
      rw [← e, hφ', ← rt_mul, ← rt_mul, ← rt_mul]
      congr 1
      group
    calc ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf (Function.update γ kv β)) φ
        = ∑ β : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β •
          Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c (Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) :=
          Finset.sum_congr rfl fun β _ => by rw [hterm]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) (Formalism.L2.NG.rt D.host.E D.R.r c
          (∑ β, (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β • Formalism.L2.NG.rt D.host.E D.R.r (ℓ β) φ')) := by
          simp only [map_sum, map_smul]
      _ = Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ := by rw [hser, back]
  have hfin := GlobalTheory.T.sum_prod_fixed_place_average_alt (ι := Σ k : Fin 2, D.nd.PlG k) (G := fun kv => GL (Fin D.R.r) (ZMod (D.host.g kv.1)))
    (fun kv β => (D.ntypes.eSer kv.1 (τ kv.1 kv.2)).coeff β) (fun γ => Formalism.L2.NG.rt D.host.E D.R.r (lf γ) φ) step
  have h1 : Formalism.L2.NG.rt D.host.E D.R.r (lf 1) φ = φ :=
    hfix (sec 1) ((hker _ (hsec 1).1).1 ((hsec 1).2)) _ (hlf 1)
  rw [finsum_eq_sum_of_fintype]
  exact hfin.trans h1

end GlobalTheory.LabFix

end
