import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

/- English proof (translation)
Take the linear combination `(-(g' * b' * a')) * h + (g' * b') * ha + (-a') * hb + (-(a' * b * b')) * hg`.
-/
theorem inv_of_mul_eq {A : Type} [CommRing A] {a a' b b' g g' : A} (h : a = g * b) (ha : a * a' = 1)
    (hb : b * b' = 1) (hg : g * g' = 1) : a' = g' * b' := by
  linear_combination (-(g' * b' * a')) * h + (g' * b') * ha + (-a') * hb + (-(a' * b * b')) * hg

variable {X X' : Scheme.{0}}

/- English proof (translation)
Establish `hy : (fun k : N.ι => (((hx k).unit⁻¹ : Γ(X, V ⊓ N.U k)ˣ) : Γ(X, V ⊓ N.U k))) ∈ Geo.Tor.secOn (pw N (-a)) V`. Introduce `i j`. Establish `h` using `GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (le_inf (inf_le_left.trans inf_le_right) inf_le_right)`. Use `inv_of_mul_eq h ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx i))).trans (map_one _))`.

Conclude with `(map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx j))).trans (map_one _))`. Use `(map_mul _ _ _).symm.trans ?_` and prove the remaining obligations. Establish `e : ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) * ((N.g i j ^ (-a) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1`. Rewrite using `[← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one]`. Conclude with `(congrArg _ e).trans (map_one _)`.

Use `⟨GlobalTheory.LB.mkSec _ hy, GlobalTheory.LB.sec_ext fun k => ?_⟩` and prove the remaining obligations. Conclude with `IsUnit.mul_val_inv (hx k)`.
-/
theorem exists_inv_of_isUnit_coord {N : LB X} {a : ℤ} {V : X.Opens} (x : SecOn (pw N a) V)
    (hx : ∀ k : N.ι, IsUnit (GlobalTheory.LB.coord x k)) :
    ∃ y : SecOn (pw N (-a)) V, secMulOn rfl x y = oneOn N (add_neg_cancel a) V := by
  have hy : (fun k : N.ι => (((hx k).unit⁻¹ : Γ(X, V ⊓ N.U k)ˣ) : Γ(X, V ⊓ N.U k))) ∈
      Geo.Tor.secOn (pw N (-a)) V := by
    intro i j
    have h := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    refine inv_of_mul_eq h ?_ ?_ ?_
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx i))).trans (map_one _))
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx j))).trans (map_one _))
    · refine (map_mul _ _ _).symm.trans ?_
      have e : ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ (-a) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1 := by
        rw [← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one]
      exact (congrArg _ e).trans (map_one _)
  refine ⟨GlobalTheory.LB.mkSec _ hy, GlobalTheory.LB.sec_ext fun k => ?_⟩
  exact IsUnit.mul_val_inv (hx k)

/- English proof (translation)
Establish `hb : V ⊓ M.U k ≤ X.basicOpen (GlobalTheory.LB.coord x k)`. Introduce `z hz`. Take `⟨z', rfl⟩` from `hπ z`. Set `j : (M.pull π).ι` to `fun _ => k`. Establish `hz₁ : z' ∈ V'` using `e.le hz.1`.

Establish `hz₂ : z' ∈ (M.pull π).U j` using `by rw [pull_U]; exact hz.2`. Take `⟨q, hq⟩` from `TopologicalSpace.Opens.mem_iSup.1 (hL.cover.ge (TopologicalSpace.Opens.mem_top z'))`. Set `O : X'.Opens` to `V' ⊓ (M.pull π).U j ⊓ L.U q`. Establish `hp : O ≤ V' ⊓ (M.pull π).U j` using `inf_le_left`. Establish `hq' : O ≤ V' ⊓ L.U q` using `inf_le_inf_right _ inf_le_left`.

Establish `hpq : O ≤ (M.pull π).U j ⊓ L.U q` using `inf_le_inf_right _ inf_le_right`. Establish `c` using `SecOn.coord_congr hL (LB.isLB_pull hM π) w hw t j q hp hq' hpq`. Rewrite `c` using `[h]`. Establish `hu : IsUnit (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j))`. Rewrite using `[c]`.

Conclude with `(Units.isUnit _).map (rs X' hpq) |>.mul ((ht q).map (rs X' hq'))`. Establish `hz' : z' ∈ X'.basicOpen (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j))`. Rewrite using `[X'.basicOpen_of_isUnit hu]`. Conclude with `⟨⟨hz₁, hz₂⟩, hq⟩`. Use `erw [Scheme.basicOpen_res] at hz'`.

Establish `hz''` using `hz'.2`. Rewrite `hz''` using `[SecOn.coord_pullLE, Scheme.basicOpen_appLE]`. Conclude with `hz''.2`. Establish `hu : IsUnit (rs X (X.basicOpen_le _) (GlobalTheory.LB.coord x k))` using `X.toRingedSpace.isUnit_res_basicOpen (GlobalTheory.LB.coord x k)`. Simplify `hu.map (rs X hb)` using `only [rs_rs, rs_self]`.
-/
theorem isUnit_coord_of_congr (π : X' ⟶ X) (hπ : Function.Surjective π) {M : LB X} {L : LB X'}
    (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L (M.pull π)) (hw : w.IsGen) {V : X.Opens}
    {V' : X'.Opens} (e : π ⁻¹ᵁ V = V') (x : SecOn M V) (t : SecOn L V')
    (h : SecOn.congr hL (LB.isLB_pull hM π) w hw V' t = SecOn.pullLE M π V V' e.ge x)
    (ht : ∀ q, IsUnit (GlobalTheory.LB.coord t q)) (k : M.ι) : IsUnit (GlobalTheory.LB.coord x k) := by
  have hb : V ⊓ M.U k ≤ X.basicOpen (GlobalTheory.LB.coord x k) := by
    intro z hz
    obtain ⟨z', rfl⟩ := hπ z
    let j : (M.pull π).ι := fun _ => k
    have hz₁ : z' ∈ V' := e.le hz.1
    have hz₂ : z' ∈ (M.pull π).U j := by rw [pull_U]; exact hz.2
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hL.cover.ge (TopologicalSpace.Opens.mem_top z'))
    let O : X'.Opens := V' ⊓ (M.pull π).U j ⊓ L.U q
    have hp : O ≤ V' ⊓ (M.pull π).U j := inf_le_left
    have hq' : O ≤ V' ⊓ L.U q := inf_le_inf_right _ inf_le_left
    have hpq : O ≤ (M.pull π).U j ⊓ L.U q := inf_le_inf_right _ inf_le_right
    have c := SecOn.coord_congr hL (LB.isLB_pull hM π) w hw t j q hp hq' hpq
    rw [h] at c
    have hu : IsUnit (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [c]
      exact (Units.isUnit _).map (rs X' hpq) |>.mul ((ht q).map (rs X' hq'))
    have hz' : z' ∈ X'.basicOpen (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [X'.basicOpen_of_isUnit hu]
      exact ⟨⟨hz₁, hz₂⟩, hq⟩
    erw [Scheme.basicOpen_res] at hz'
    have hz'' := hz'.2
    rw [SecOn.coord_pullLE, Scheme.basicOpen_appLE] at hz''
    exact hz''.2
  have hu : IsUnit (rs X (X.basicOpen_le _) (GlobalTheory.LB.coord x k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (GlobalTheory.LB.coord x k)
  simpa only [rs_rs, rs_self] using hu.map (rs X hb)

variable {R : Type} [CommRing R] (I : Ideal R)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx` using `[RingHom.mem_ker]`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite using `[mem_nilradical]`.

Use `⟨2, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow, Ideal.Quotient.eq_zero_iff_mem]`. Establish `hy2 : y ^ 2 ∈ I ^ (e + 1) * I ^ (e + 1)`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul hx hx`.

Rewrite `hy2` using `[← pow_add]`. Conclude with `Ideal.pow_le_pow_right (by omega) hy2`.
-/
theorem ker_factor_le_nilradical (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    RingHom.ker (Ideal.Quotient.factor h) ≤ nilradical (R ⧸ I ^ (e + 1 + 1)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hy2 : y ^ 2 ∈ I ^ (e + 1) * I ^ (e + 1) := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hx
  rw [← pow_add] at hy2
  exact Ideal.pow_le_pow_right (by omega) hy2

/- English proof (translation)
Use `delta ReciprocityTheory.ChartRestriction.G.Out.thickTrans`. Establish `key : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), Function.Surjective φ → RingHom.ker φ ≤ nilradical A → Surjective (Spec.map (CommRingCat.ofHom φ))`. Introduce `A B _ _ φ hφ hker`. Prove the components needed by the constructor for the conclusion. Introduce `p`.

Use `haveI := p.isPrime`. Establish `hk : RingHom.ker φ ≤ p.asIdeal` using `le_trans hker (nilradical_le_prime p.asIdeal)`. Use `⟨⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩, ?_⟩` and prove the remaining obligations. Use `show PrimeSpectrum.comap φ ⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩ = p`. Use `ext1`.

Use `show Ideal.comap φ (Ideal.map φ p.asIdeal) = p.asIdeal`. Rewrite using `[Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hk]`. Conclude with `key _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_le_nilradical I e _)`.
-/
theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  delta ReciprocityTheory.ChartRestriction.G.Out.thickTrans
  have key : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), Function.Surjective φ →
      RingHom.ker φ ≤ nilradical A → Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    intro A B _ _ φ hφ hker
    constructor
    intro p
    haveI := p.isPrime
    have hk : RingHom.ker φ ≤ p.asIdeal := le_trans hker (nilradical_le_prime p.asIdeal)
    refine ⟨⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩, ?_⟩
    show PrimeSpectrum.comap φ ⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩ = p
    ext1
    show Ideal.comap φ (Ideal.map φ p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hk]
  exact key _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_le_nilradical I e _)

variable (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))

include hβ in

/- English proof (translation)
Conclude with `(MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans I e)).surj`.
-/
theorem surjective_tower (e : ℕ) : Function.Surjective (β e) := by
  exact (MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans I e)).surj

/- English proof (translation)
The claim follows from `isUnit_coord_of_congr (β e) (surjective_tower I Y β hβ e) (hL e).1 (hL (e + 1)).1 (w e) (hL e).2 h x (redL I Y β hβ L w hL e V V' h.ge x) ((SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 V')).apply_symm_apply _) ht k`.
-/
theorem isUnit_coord_of_redL (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) {V : (Y (e + 1)).left.Opens}
    {V' : (Y e).left.Opens} (h : β e ⁻¹ᵁ V = V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (ht : ∀ q, IsUnit (SecOnR.coord (redL I Y β hβ L w hL e V V' h.ge x) q)) (k : (L (e + 1)).ι) :
    IsUnit (SecOnR.coord x k) :=
  isUnit_coord_of_congr (β e) (surjective_tower I Y β hβ e) (hL e).1 (hL (e + 1)).1 (w e) (hL e).2 h
    x (redL I Y β hβ L w hL e V V' h.ge x)
    ((SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
      (hL e).2 V')).apply_symm_apply _) ht k

/- English proof (translation)
Introduce `R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa`. Establish `hge : ∀ e (S : Finset (Fin (m + 1))), D e S ≤ β e ⁻¹ᵁ D (e + 1) S` using `fun e S => (hDβ e S).ge`. Establish `hsurj : ∀ e (S : Finset (Fin (m + 1))), S.Nonempty → Function.Surjective (red I Y N D β hβ v hN hge (d : ℤ) e S)` using `fun e S hS => (redL_surjective_ker R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ)) (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S) (hDβ e S) (hDa (e + 1) S hS)).1`. Establish `hl : ∀ e (S : Finset (Fin (m + 1))) (t : SecOn (pw (N e) (d : ℤ)) (D e S)), ∃ x : SecOn (pw (N (e + 1)) (d : ℤ)) (D (e + 1) S), S.Nonempty → red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ x) = SecOnR.of _ _ _ t`. Introduce `e S t`.

Distinguish the cases in `hS : S.Nonempty`. Take `⟨x, hx⟩` from `hsurj e S hS (SecOnR.of _ _ _ t)`. Conclude with `⟨(SecOnR.of _ _ _).symm x, fun _ => hx⟩`. Conclude with `⟨0, fun h => absurd h hS⟩`. Use `choose lf hlf using hl`.

Set `sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)` to `fun e j S => Nat.rec (motive := fun e => SecOn (pw (N e) (d : ℤ)) (D e S)) (GlobalTheory.LB.ofSec (s j) (D 0 S)) (fun e t => lf e S t) e`. Use `⟨sh, fun j S _ => rfl, fun e j S hS => hlf e S _ hS, fun e i S hi => exists_inv_of_isUnit_coord _ ?_⟩` and prove the remaining obligations. Proceed by induction on `e with`. Consider the case `zero`. Introduce `k`.

Establish `hle : D 0 S ≤ nonzeroLocus (s i)`. Rewrite using `[hD0]`. Conclude with `iInf₂_le i hi`. Conclude with `SecOn.isUnit_rs_of_le_nonzeroLocus (s i) k (inf_le_right : D 0 S ⊓ (N 0).U k ≤ (N 0).U k) (inf_le_left.trans hle)`. Consider the case `succ e ih`.

Introduce `k`. Use `isUnit_coord_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ)) (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (hDβ e S) (SecOnR.of _ _ _ (sh (e + 1) i S)) (fun q => ?_) k` and prove the remaining obligations. Establish `hr : red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S)) = SecOnR.of _ _ _ (sh e i S)` using `hlf e S (sh e i S) ⟨i, hi⟩`. Express the relevant statement in the definitionally equal form `IsUnit (SecOnR.coord (red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S))) q)`. Rewrite using `[hr]`.

Conclude with `ih q`.
-/
theorem exists_lifts_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hge : ∀ e (S : Finset (Fin (m + 1))), D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have hsurj : ∀ e (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red I Y N D β hβ v hN hge (d : ℤ) e S) := fun e S hS =>
    (redL_surjective_ker R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)).1
  have hl : ∀ e (S : Finset (Fin (m + 1))) (t : SecOn (pw (N e) (d : ℤ)) (D e S)),
      ∃ x : SecOn (pw (N (e + 1)) (d : ℤ)) (D (e + 1) S), S.Nonempty →
        red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ x) = SecOnR.of _ _ _ t := by
    intro e S t
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hsurj e S hS (SecOnR.of _ _ _ t)
      exact ⟨(SecOnR.of _ _ _).symm x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose lf hlf using hl
  let sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S) :=
    fun e j S => Nat.rec (motive := fun e => SecOn (pw (N e) (d : ℤ)) (D e S))
      (GlobalTheory.LB.ofSec (s j) (D 0 S)) (fun e t => lf e S t) e
  refine ⟨sh, fun j S _ => rfl, fun e j S hS => hlf e S _ hS, fun e i S hi =>
    exists_inv_of_isUnit_coord _ ?_⟩
  induction e with
  | zero =>
    intro k
    have hle : D 0 S ≤ nonzeroLocus (s i) := by
      rw [hD0]
      exact iInf₂_le i hi
    exact SecOn.isUnit_rs_of_le_nonzeroLocus (s i) k (inf_le_right : D 0 S ⊓ (N 0).U k ≤ (N 0).U k)
      (inf_le_left.trans hle)
  | succ e ih =>
    intro k
    refine isUnit_coord_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
      (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (hDβ e S)
      (SecOnR.of _ _ _ (sh (e + 1) i S)) (fun q => ?_) k
    have hr : red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S)) =
        SecOnR.of _ _ _ (sh e i S) := hlf e S (sh e i S) ⟨i, hi⟩
    change IsUnit (SecOnR.coord (red I Y N D β hβ v hN hge (d : ℤ) e S
      (SecOnR.of _ _ _ (sh (e + 1) i S))) q)
    rw [hr]
    exact ih q

end GlobalTheory.CompanionTheory.FormalAlg.Lift
