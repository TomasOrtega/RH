import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionLimit

section Alg

variable {R : Type} [CommRing R] (I : Ideal R)

/- English proof (translation)
Use `choose x hx using fun e => Ideal.Quotient.mk_surjective (c e)`. Establish `h1 : ∀ e, x e - x (e + 1) ∈ I ^ (e + 1)` using `fun e => by`. Rewrite using `[← Ideal.Quotient.eq, hx, ← hc e, ← hx, Ideal.Quotient.factor_mk]`. Establish `h2 : ∀ m n, m ≤ n → x m - x n ∈ I ^ m` using `fun m n h => by`. Proceed by induction on `n, h using Nat.le_induction with`.

Consider the case `base => simp`. Consider the case `succ n hmn ih`. Use `(I ^ m).add_mem ih (Ideal.pow_le_pow_right (hmn.trans (Nat.le_succ n)) (h1 n))` as an intermediate fact. Simplify using `using this`. Take `⟨a, ha⟩` from `IsPrecomplete.prec (I := I) (M := R) inferInstance (f := x) (fun {m n} h => by`.

Rewrite using `[SModEq.sub_mem]`. Simplify using `using h2 m n h)`. Use `⟨a, fun e => ?_⟩` and prove the remaining obligations. Establish `h3 : x (e + 1) - a ∈ I ^ (e + 1)`. Use `ha (e + 1)` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem]`. Simplify using `using this`. Rewrite using `[← hx, eq_comm, Ideal.Quotient.eq]`. Simplify using `using (I ^ (e + 1)).add_mem (h1 e) h3`.
-/
theorem exists_lim [IsPrecomplete I R] (c : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1)) = c e) :
    ∃ a : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = c e := by
  choose x hx using fun e => Ideal.Quotient.mk_surjective (c e)
  have h1 : ∀ e, x e - x (e + 1) ∈ I ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hx, ← hc e, ← hx, Ideal.Quotient.factor_mk]
  have h2 : ∀ m n, m ≤ n → x m - x n ∈ I ^ m := fun m n h => by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (I ^ m).add_mem ih (Ideal.pow_le_pow_right (hmn.trans (Nat.le_succ n)) (h1 n))
      simpa using this
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := x) (fun {m n} h => by
    rw [SModEq.sub_mem]; simpa using h2 m n h)
  refine ⟨a, fun e => ?_⟩
  have h3 : x (e + 1) - a ∈ I ^ (e + 1) := by
    have := ha (e + 1)
    rw [SModEq.sub_mem] at this
    simpa using this
  rw [← hx, eq_comm, Ideal.Quotient.eq]
  simpa using (I ^ (e + 1)).add_mem (h1 e) h3

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero]`. Simplify using `using Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))`.
-/
theorem eq_of_mk_eq [IsHausdorff I R] {a b : R}
    (h : ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = Ideal.Quotient.mk (I ^ (e + 1)) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.zero]
  simpa using Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

end Alg

section Calc

variable {X Y Y' : Scheme.{0}} {L : LB X}

/- English proof (translation)
Take `rfl : (fun k => h ≫ φ k) = φ'` from `funext e`. Conclude with `⟨pullSec L φ ε s h, fun _ _ => rfl, fun Z r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩`.
-/
theorem exists_pull {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨pullSec L φ ε s h, fun _ _ => rfl, fun Z r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

def linSec {M : LB Y} {N : ℕ} (c : Fin N → Γ(Y, ⊤)) (t : Fin N → LB.Sec M) : LB.Sec M where
  f j := ∑ i, resTop _ (c i) * (t i).f j
  compat i j := by
    rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (SecOps.secScale (c k) (t k)).compat i j

variable {C : Type} [CommRing C] {n N : ℕ}

def Rep (π : Y ⟶ X) (f : Y ⟶ Sp C) (β : Fin N → H0 L n)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (n : ℤ)))) (c : Fin N → C) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
    sval s r z J = ∑ i, cst (r ≫ f) z (c i) * sval (β i) (r ≫ π) z J

/- English proof (translation)
Substitute `hπ hf` using the available equality. Introduce `s'`. Take `⟨s, -, hs⟩` from `exists_pull s' e.inv (fun _ : Fin 1 => π) (fun _ => e.inv_hom_id_assoc π)`. Establish `key : ∀ c, Rep (e.hom ≫ π) (e.hom ≫ f) β s' c ↔ Rep π f β s c` using `fun c => by`. Prove the components needed by the constructor for the conclusion.

Introduce `h Z r z J hJ`. Rewrite using `[hs Z r z J hJ, h Z _ z J hJ]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc]`. Introduce `h Z r z J hJ`. Use `h Z (r ≫ e.hom) z J hJ` as an intermediate fact.

Rewrite `this` using `[hs Z _ z J hJ]`. Simplify `this` using `only [Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Simplify using `only [key]`. Conclude with `H s`.
-/
theorem rep_transport {π : Y ⟶ X} {f : Y ⟶ Sp C} {β : Fin N → H0 L n} (e : Y' ≅ Y)
    {π' : Y' ⟶ X} {f' : Y' ⟶ Sp C} (hπ : e.hom ≫ π = π') (hf : e.hom ≫ f = f')
    (H : ∀ s, ∃! c, Rep π f β s c) : ∀ s, ∃! c, Rep π' f' β s c := by
  subst hπ hf
  intro s'
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (fun _ : Fin 1 => π) (fun _ => e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ π) (e.hom ≫ f) β s' c ↔ Rep π f β s c := fun c => by
    constructor
    · intro h Z r z J hJ
      rw [hs Z r z J hJ, h Z _ z J hJ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · intro h Z r z J hJ
      have := h Z (r ≫ e.hom) z J hJ
      rw [hs Z _ z J hJ] at this
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  simp only [key]
  exact H s

/- English proof (translation)
Rewrite using `[SectionScalarValuation.sval_lin (s := linSec (fun i => scal f (c i)) t) (fun i => scal f (c i)) t (fun _ => rfl) r z hJ]`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r f z ⊤ trivial _)`.
-/
theorem sval_linSec {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (f : Y ⟶ Sp C) (c : Fin N → C)
    (t : Fin N → LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    sval (linSec (fun i => scal f (c i)) t) r z J = ∑ i, cst (r ≫ f) z (c i) * sval (t i) r z J := by
  rw [SectionScalarValuation.sval_lin (s := linSec (fun i => scal f (c i)) t) (fun i => scal f (c i)) t (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r f z ⊤ trivial _)

end Calc

/- English proof (translation)
Establish `hL` using `P.isLB`. Take `⟨U, hU, b, hb⟩` from `hS (Spec (CommRingCat.of R)) P n hn (closedPoint R)`. Take `rfl : U = ⊤` from `eq_top_of_closedPoint_mem U hU`. Set `V` to `overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤`. Set `t₀ : Spec (CommRingCat.of R) ⟶ V.left` to `(Spec (CommRingCat.of R)).topIso.inv`.

Establish `ht : t₀ ≫ V.hom = 𝟙 _` using `by show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _`. Rewrite using `[Category.comp_id]`. Conclude with `(Spec (CommRingCat.of R)).topIso.inv_hom_id`. Establish `ht' : V.hom ≫ t₀ = 𝟙 _` using `by show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _`. Rewrite using `[Category.comp_id]`.

Conclude with `(Spec (CommRingCat.of R)).topIso.hom_inv_id`. Set `u : P.A ⟶ V` to `Over.homMk (P.A.hom ≫ t₀) (by rw [Category.assoc, ht, Category.comp_id])`. Establish `hu : snd V P.A ≫ u = fst V P.A` using `Over.OverMorphism.ext (by show (snd V P.A).left ≫ P.A.hom ≫ t₀ = (fst V P.A).left`. Rewrite using `[← Category.assoc, Over.w (snd V P.A), ← Over.w (fst V P.A), Category.assoc, ht', Category.comp_id])`. Establish `e₁ : lift u (𝟙 P.A) ≫ snd V P.A = 𝟙 _` using `lift_snd _ _`.

Establish `e₂ : snd V P.A ≫ lift u (𝟙 P.A) = 𝟙 _`. Rewrite using `[comp_lift, hu, Category.comp_id, lift_fst_snd]`. Use `choose β hβ0 hβ using fun i => exists_pull (K := Fin 1) (b i) (lift u (𝟙 P.A)).left (fun _ => 𝟙 P.A.left) (fun _ => congrArg CommaMorphism.left e₁)`. Use `⟨_, β, fun C _ q Y π f hp => ?_⟩` and prove the remaining obligations. Set `t : Spec (CommRingCat.of C) ⟶ V.left` to `q ≫ t₀`.

Establish `hq : (baseAt t).hom = q` using `by show (q ≫ t₀) ≫ V.hom = q`. Rewrite using `[Category.assoc, ht, Category.comp_id]`. Use `choose b' hb0 hb' using fun i => exists_pull (K := Fin 1) (b i) (homAt t ▷ P.A).left (fun _ => (snd (baseAt t) P.A).left) (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))`. Take `⟨hli, hsp⟩` from `hb C t b' (fun i j => hb0 i j _)`. Establish `e₃ : snd (baseAt t) P.A ≫ lift u (𝟙 P.A) = homAt t ▷ P.A`.

Rewrite using `[← whiskerRight_snd (homAt t) P.A, Category.assoc, e₂, Category.comp_id]`. Establish `e₄ : (snd (baseAt t) P.A).left ≫ (lift u (𝟙 P.A)).left = (homAt t ▷ P.A).left` using `congrArg CommaMorphism.left e₃`. Establish `hp' : IsPullback f π (baseAt t).hom P.A.hom` using `hq ▸ hp`. Use `rep_transport (Y := (baseAt t ⊗ P.A).left) (π := (snd (baseAt t) P.A).left) (f := (fst (baseAt t) P.A).left) hp'.isoPullback hp'.isoPullback_hom_snd hp'.isoPullback_hom_fst fun s => ?_` and prove the remaining obligations. Establish `bij` using `ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv`.

Establish `hv : ∀ (c : Fin (n ^ P.g) → C) (Z : Scheme.{0}) (r : Z ⟶ (baseAt t ⊗ P.A).left) (z : Z) (J), Good P.L z J → sval (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b') r z J = ∑ i, cst (r ≫ (fst (baseAt t) P.A).left) z (c i) * sval (β i) (r ≫ (snd (baseAt t) P.A).left) z J` using `fun c Z r z J hJ => by`. Rewrite using `[sval_linSec _ _ _ _ _ hJ]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hb' i Z r z J hJ, hβ i Z _ z J hJ, Category.assoc, e₄]`. Establish `key : ∀ c : Fin (n ^ P.g) → C, Rep (snd (baseAt t) P.A).left (fst (baseAt t) P.A).left β s c ↔ ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) • (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s` using `fun c => by`.

Establish `ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) • (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j = (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b').f j` using `fun j => by`. Rewrite using `[Submodule.coe_sum, Finset.sum_apply]`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `Subtype.ext (funext fun j => (ev j).trans ?_)` and prove the remaining obligations. Conclude with `sec_ext_val hL (fun y J hJ => (hv c _ _ y J hJ).trans (h _ _ y J hJ).symm) j`. Introduce `h Z r z J hJ`. Establish `: s = linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b'` using `SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)`. Rewrite using `[this]`.

Conclude with `hv c Z r z J hJ`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))`. Use `choose a ha using fun i => bij.2 (r i)`. Take `rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a i)) = r` from `funext ha`. Use `⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩` and prove the remaining obligations.

Conclude with `Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i`.
-/
theorem exists_basis (hS : SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : ℕ) (β : Fin N → H0 P.L n), ∀ (C : Type) [CommRing C] (q : Sp C ⟶ Sp R) (Y : Scheme.{0})
      (π : Y ⟶ P.A.left) (f : Y ⟶ Sp C), IsPullback f π q P.A.hom → ∀ s, ∃! c, Rep π f β s c := by
  have hL := P.isLB
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P n hn (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let V := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let t₀ : Spec (CommRingCat.of R) ⟶ V.left := (Spec (CommRingCat.of R)).topIso.inv
  have ht : t₀ ≫ V.hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have ht' : V.hom ≫ t₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ V := Over.homMk (P.A.hom ≫ t₀) (by rw [Category.assoc, ht, Category.comp_id])
  have hu : snd V P.A ≫ u = fst V P.A := Over.OverMorphism.ext (by
    show (snd V P.A).left ≫ P.A.hom ≫ t₀ = (fst V P.A).left
    rw [← Category.assoc, Over.w (snd V P.A), ← Over.w (fst V P.A), Category.assoc, ht', Category.comp_id])
  have e₁ : lift u (𝟙 P.A) ≫ snd V P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd V P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  choose β hβ0 hβ using fun i => exists_pull (K := Fin 1) (b i) (lift u (𝟙 P.A)).left (fun _ => 𝟙 P.A.left)
    (fun _ => congrArg CommaMorphism.left e₁)
  refine ⟨_, β, fun C _ q Y π f hp => ?_⟩
  let t : Spec (CommRingCat.of C) ⟶ V.left := q ≫ t₀
  have hq : (baseAt t).hom = q := by
    show (q ≫ t₀) ≫ V.hom = q
    rw [Category.assoc, ht, Category.comp_id]
  choose b' hb0 hb' using fun i => exists_pull (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  obtain ⟨hli, hsp⟩ := hb C t b' (fun i j => hb0 i j _)
  have e₃ : snd (baseAt t) P.A ≫ lift u (𝟙 P.A) = homAt t ▷ P.A := by
    rw [← whiskerRight_snd (homAt t) P.A, Category.assoc, e₂, Category.comp_id]
  have e₄ : (snd (baseAt t) P.A).left ≫ (lift u (𝟙 P.A)).left = (homAt t ▷ P.A).left :=
    congrArg CommaMorphism.left e₃
  have hp' : IsPullback f π (baseAt t).hom P.A.hom := hq ▸ hp
  refine rep_transport (Y := (baseAt t ⊗ P.A).left) (π := (snd (baseAt t) P.A).left)
    (f := (fst (baseAt t) P.A).left) hp'.isoPullback hp'.isoPullback_hom_snd hp'.isoPullback_hom_fst fun s => ?_
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  have hv : ∀ (c : Fin (n ^ P.g) → C) (Z : Scheme.{0}) (r : Z ⟶ (baseAt t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sval (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b') r z J =
        ∑ i, cst (r ≫ (fst (baseAt t) P.A).left) z (c i) * sval (β i) (r ≫ (snd (baseAt t) P.A).left) z J :=
    fun c Z r z J hJ => by
      rw [sval_linSec _ _ _ _ _ hJ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb' i Z r z J hJ, hβ i Z _ z J hJ, Category.assoc, e₄]
  have key : ∀ c : Fin (n ^ P.g) → C, Rep (snd (baseAt t) P.A).left (fst (baseAt t) P.A).left β s c ↔
      ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
    have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
        (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b').f j := fun j => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    constructor
    · intro h
      refine Subtype.ext (funext fun j => (ev j).trans ?_)
      exact sec_ext_val hL (fun y J hJ => (hv c _ _ y J hJ).trans (h _ _ y J hJ).symm) j
    · intro h Z r z J hJ
      have : s = linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b' :=
        SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)
      rw [this]
      exact hv c Z r z J hJ
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
  choose a ha using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a i)) = r := funext ha
  refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i

/- English proof (translation)
Introduce `hS R _ _ _ I _ P n hn s hs`. Establish `hL` using `P.isLB`. Take `⟨N, β, hβ⟩` from `exists_basis hS R P n hn`. Establish `hpe : ∀ e, IsPullback (thickObj R I e P.A).hom (fstG I e P.A).left (thick R I e) P.A.hom` using `fun e => (IsPullback.of_hasPullback P.A.hom (thick R I e)).flip`. Use `choose c hc hcu using fun e => hβ _ _ _ _ _ (hpe e) (s e)`.

Establish `hcomp : ∀ e i, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i) = c e i` using `fun e => congrFun (hcu e (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i)) fun Z r z J hJ => by`. Establish `h₁ : thickMap R I e P.A ≫ (thickObj R I (e + 1) P.A).hom = (thickObj R I e P.A).hom ≫ thickTrans R I e` using `pullback.lift_snd _ _ _`. Establish `h₂ : thickMap R I e P.A ≫ (fstG I (e + 1) P.A).left = (fstG I e P.A).left` using `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`. Rewrite using `[← hs e Z r z J hJ, hc (e + 1) Z _ z J hJ, Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc]`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _))`.

Use `choose a ha using fun i => exists_lim I (fun e => c e i) (fun e => hcomp e i)`. Establish `down : ∀ (σ : H0 P.L n) (a : Fin N → R), Rep (𝟙 _) P.A.hom β σ a → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J → sval σ (r ≫ (fstG I e P.A).left) z J = ∑ i, cst (r ≫ (thickObj R I e P.A).hom) z (Ideal.Quotient. …` using `fun σ a h e Z r z J hJ => by`. Rewrite using `[h Z _ z J hJ, Category.comp_id, Category.assoc, ← (hpe e).w, ← Category.assoc]`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _)`. Establish `hlin : Rep (𝟙 _) P.A.hom β (linSec (fun i => scal P.A.hom (a i)) β) a` using `fun Z r z J hJ => by`.

Rewrite using `[sval_linSec _ _ _ _ _ hJ, Category.comp_id]`. Use `⟨linSec (fun i => scal P.A.hom (a i)) β, fun e Z r z J hJ => ?_, fun σ hσ => ?_⟩` and prove the remaining obligations. Rewrite using `[down _ a hlin e Z r z J hJ, hc e Z r z J hJ]`. Simplify using `only [ha]`. Take `⟨a', ha', -⟩` from `hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ`.

Establish `: a' = a` using `funext fun i => eq_of_mk_eq I fun e => by`. Rewrite using `[ha]`. Conclude with `congrFun (hcu e (fun i => Ideal.Quotient.mk (I ^ (e + 1)) (a' i)) fun Z r z J hJ => (hσ e Z r z J hJ).symm.trans (down σ a' ha' e Z r z J hJ)) i`. Substitute `this` using the available equality. Conclude with `SecOps.sec_ext (sec_ext_val hL fun y J hJ => (ha' _ _ y J hJ).trans (hlin _ _ y J hJ).symm)`.
-/
theorem existsUnique_sec_of_compatible : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = Geo.Tor.sval (s e) r z J) → ∃! σ : H0 P.L n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval σ (r ≫ (fstG I e P.A).left) z J = Geo.Tor.sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hL := P.isLB
  obtain ⟨N, β, hβ⟩ := exists_basis hS R P n hn
  have hpe : ∀ e, IsPullback (thickObj R I e P.A).hom (fstG I e P.A).left (thick R I e) P.A.hom :=
    fun e => (IsPullback.of_hasPullback P.A.hom (thick R I e)).flip
  choose c hc hcu using fun e => hβ _ _ _ _ _ (hpe e) (s e)
  have hcomp : ∀ e i, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i) = c e i :=
    fun e => congrFun (hcu e (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (c (e + 1) i)) fun Z r z J hJ => by
        have h₁ : thickMap R I e P.A ≫ (thickObj R I (e + 1) P.A).hom =
            (thickObj R I e P.A).hom ≫ thickTrans R I e := pullback.lift_snd _ _ _
        have h₂ : thickMap R I e P.A ≫ (fstG I (e + 1) P.A).left = (fstG I e P.A).left :=
          (pullback.lift_fst _ _ _).trans (Category.comp_id _)
        rw [← hs e Z r z J hJ, hc (e + 1) Z _ z J hJ, Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc]
        exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _))
  choose a ha using fun i => exists_lim I (fun e => c e i) (fun e => hcomp e i)
  have down : ∀ (σ : H0 P.L n) (a : Fin N → R), Rep (𝟙 _) P.A.hom β σ a → ∀ (e : ℕ) (Z : Scheme.{0})
      (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval σ (r ≫ (fstG I e P.A).left) z J = ∑ i, cst (r ≫ (thickObj R I e P.A).hom) z
        (Ideal.Quotient.mk (I ^ (e + 1)) (a i)) * sval (β i) (r ≫ (fstG I e P.A).left) z J :=
    fun σ a h e Z r z J hJ => by
      rw [h Z _ z J hJ, Category.comp_id, Category.assoc, ← (hpe e).w, ← Category.assoc]
      exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _)
  have hlin : Rep (𝟙 _) P.A.hom β (linSec (fun i => scal P.A.hom (a i)) β) a := fun Z r z J hJ => by
    rw [sval_linSec _ _ _ _ _ hJ, Category.comp_id]
  refine ⟨linSec (fun i => scal P.A.hom (a i)) β, fun e Z r z J hJ => ?_, fun σ hσ => ?_⟩
  · rw [down _ a hlin e Z r z J hJ, hc e Z r z J hJ]
    simp only [ha]
  · obtain ⟨a', ha', -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    have : a' = a := funext fun i => eq_of_mk_eq I fun e => by
      rw [ha]
      exact congrFun (hcu e (fun i => Ideal.Quotient.mk (I ^ (e + 1)) (a' i)) fun Z r z J hJ =>
        (hσ e Z r z J hJ).symm.trans (down σ a' ha' e Z r z J hJ)) i
    subst this
    exact SecOps.sec_ext (sec_ext_val hL fun y J hJ => (ha' _ _ y J hJ).trans (hlin _ _ y J hJ).symm)

end GlobalTheory.SectionLimit
