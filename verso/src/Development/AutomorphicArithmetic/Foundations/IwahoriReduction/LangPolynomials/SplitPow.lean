import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FixedIntegersIsUnitOfNotMemPrimeSpan
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.FrobEx
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralLimitCompatibleModPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.CoboundaryRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Take `⟨g, hg⟩` from `IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)`. Rewrite `hg` using `[Nat.card_eq_fintype_card, ZMod.card_units]`. Establish `h1 : IsPrimitiveRoot (g : ZMod l) (l - 1)`. Rewrite using `[IsPrimitiveRoot.coe_units_iff, ← hg]`. Conclude with `IsPrimitiveRoot.orderOf g`.

Establish `h2` using `h1.map_of_injective (f := WittVector.teichmuller l) (fun a b h => by`. Simplify using `using congrArg (fun w : WittVector l (ZMod l) => w.coeff 0) h)`. Establish `h3` using `h2.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l))`. Introduce `a b h`.

Rewrite `h` using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) b]`. Conclude with `Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)`. Establish `h4` using `h3.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) hinj`. Use `haveI : NeZero (l - 1) := ⟨by have := (Fact.out : l.Prime).two_le; omega⟩`. Take `⟨i, -, hi⟩` from `h4.eq_pow_of_pow_eq_one hx`.

Rewrite using `[← hi]`. Conclude with `c.O.pow_mem (c.O.algebraMap_mem _) i`.
-/
private theorem root_mem (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have h1 : IsPrimitiveRoot (g : ZMod l) (l - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hg]; exact IsPrimitiveRoot.orderOf g
  have h2 := h1.map_of_injective (f := WittVector.teichmuller l) (fun a b h => by
    simpa using congrArg (fun w : WittVector l (ZMod l) => w.coeff 0) h)
  have h3 := h2.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    intro a b h
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) b] at h
    exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)
  have h4 := h3.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) hinj
  haveI : NeZero (l - 1) := ⟨by have := (Fact.out : l.Prime).two_le; omega⟩
  obtain ⟨i, -, hi⟩ := h4.eq_pow_of_pow_eq_one hx
  rw [← hi]
  exact c.O.pow_mem (c.O.algebraMap_mem _) i

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ← norm_neg y]`. Conclude with `IsUltrametricDist.norm_add_le_max _ _`.
-/
private theorem nsub (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']`. Conclude with `Padic.norm_int_le_one m`.
-/
private theorem nint (m : ℤ) : ‖((m : ℤ) : Qbar l)‖ ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_int_le_one m

/- English proof (translation)
Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']`. Conclude with `Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)`.
-/
private theorem nnat {m : ℕ} (h : ¬ l ∣ m) : ‖((m : ℕ) : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)

/- English proof (translation)
Take `⟨⟨β⟩, h⟩` from `pBasEx l c`. Take `⟨v, hv⟩ : ∃ v : Fin β.d → ℤ_[l], ∑ i, v i • β.e i = ⟨x, hx⟩` from `⟨_, β.e.sum_repr _⟩`. Establish `h1` using `congrArg (fun y : c.O => (y : Qbar l)) hv`. Simplify using `only [AddSubmonoidClass.coe_finset_sum] at h1`. Rewrite using `[← h1]`.

Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_` and prove the remaining obligations. Establish `e : ((v i • β.e i : c.O) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) * β.val i`. Rewrite using `[← show algebraMap ℤ_[l] (Qbar l) (v i) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) from IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) (v i), ← Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[e, norm_mul, norm_algebraMap']`.

Conclude with `mul_le_one₀ (v i).2 (norm_nonneg _) ((h β).1 i)`.
-/
private theorem nO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  obtain ⟨v, hv⟩ : ∃ v : Fin β.d → ℤ_[l], ∑ i, v i • β.e i = ⟨x, hx⟩ := ⟨_, β.e.sum_repr _⟩
  have h1 := congrArg (fun y : c.O => (y : Qbar l)) hv
  simp only [AddSubmonoidClass.coe_finset_sum] at h1
  rw [← h1]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  have e : ((v i • β.e i : c.O) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) * β.val i := by
    rw [← show algebraMap ℤ_[l] (Qbar l) (v i) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) from
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) (v i), ← Algebra.smul_def]
    rfl
  rw [e, norm_mul, norm_algebraMap']
  exact mul_le_one₀ (v i).2 (norm_nonneg _) ((h β).1 i)

/- English proof (translation)
Take `⟨⟨β⟩, h⟩` from `pBasEx l c`. Conclude with `(h β).2.2.2 x hx h1`.
-/
private theorem invO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) (h1 : ‖x‖ = 1) : x⁻¹ ∈ c.O := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  exact (h β).2.2.2 x hx h1

/- English proof (translation)
Introduce `h`. Establish `hc` using `ZMod.val_coe_unit_coprime x`. Establish `hd : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r)` using `Nat.dvd_gcd h (dvd_pow_self l (by omega))`. Rewrite `hd` using `[Nat.Coprime.gcd_eq_one hc]`. Conclude with `(Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 hd)`.
-/
private theorem ndv {r : ℕ} (hr : 1 ≤ r) (x : (ZMod (l ^ r))ˣ) : ¬ l ∣ (x : ZMod (l ^ r)).val := by
  intro h
  have hc := ZMod.val_coe_unit_coprime x
  have hd : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r) := Nat.dvd_gcd h (dvd_pow_self l (by omega))
  rw [Nat.Coprime.gcd_eq_one hc] at hd
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 hd)

/- English proof (translation)
Establish `hm : (m : ZMod l) ≠ 0` using `by rwa [Ne, ZMod.natCast_eq_zero_iff]`. Rewrite using `[← map_pow, ZMod.pow_card_sub_one_eq_one hm, map_one]`.
-/
private theorem phi_pow (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : φ (m : ZMod l) ^ (l - 1) = 1 := by
  have hm : (m : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one hm, map_one]

/- English proof (translation)
Establish `h3 : ‖φ (m : ZMod l)‖ ^ (l - 1) = 1` using `by rw [← norm_pow, phi_pow φ h, norm_one]`. Establish `hl : l - 1 ≠ 0` using `by have := (Fact.out : l.Prime).two_le; omega`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 h3`.
-/
private theorem nphi (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : ‖φ (m : ZMod l)‖ = 1 := by
  have h3 : ‖φ (m : ZMod l)‖ ^ (l - 1) = 1 := by rw [← norm_pow, phi_pow φ h, norm_one]
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 h3

private noncomputable def E (φ : DirichletCharacter (Qbar l) l) (k a : ℕ) : Qbar l :=
  (φ (a : ZMod l))⁻¹ * ((a : Qbar l) ^ k)⁻¹

/- English proof (translation)
Simplify using `only [E, Nat.cast_mul, map_mul, mul_pow, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem E_mul (φ : DirichletCharacter (Qbar l) l) (k a b : ℕ) : E φ k (a * b) = E φ k a * E φ k b := by
  simp only [E, Nat.cast_mul, map_mul, mul_pow, mul_inv]
  ring

/- English proof (translation)
The claim follows from `c.O.mul_mem (invO c (root_mem c (phi_pow φ ha)) (nphi φ ha)) (invO c (c.O.pow_mem (natCast_mem c.O a) k) (by rw [norm_pow, nnat ha, one_pow]))`.
-/
private theorem E_mem (c : Coef l) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {a : ℕ} (ha : ¬ l ∣ a) : E φ k a ∈ c.O :=
  c.O.mul_mem (invO c (root_mem c (phi_pow φ ha)) (nphi φ ha))
    (invO c (c.O.pow_mem (natCast_mem c.O a) k) (by rw [norm_pow, nnat ha, one_pow]))

/- English proof (translation)
Establish `hphi : (a : ZMod l) = (b : ZMod l)` using `(ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (dvd_pow_self l (by omega)))`. Take `⟨m, hm⟩` from `Nat.modEq_iff_dvd.1 (h.pow k)`. Establish `hmQ : (b : Qbar l) ^ k - (a : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l)`. Use `congrArg (fun z : ℤ => (z : Qbar l)) hm` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `nz : ∀ z : Qbar l, ‖z‖ = 1 → z ≠ 0` using `fun z hz h => by rw [h, norm_zero] at hz; exact zero_ne_one hz`. Establish `haQ` using `nz _ (nnat ha)`. Establish `hbQ` using `nz _ (nnat hb)`. Establish `hpb` using `nz _ (nphi φ hb)`.

Establish `key : E φ k a - E φ k b = (φ (b : ZMod l))⁻¹ * ((a : Qbar l) ^ k)⁻¹ * ((b : Qbar l) ^ k)⁻¹ * ((b : Qbar l) ^ k - (a : Qbar l) ^ k)`. Simplify using `only [E]`. Rewrite using `[hphi]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[key, hmQ]`.

Simplify using `only [norm_mul, norm_inv, norm_pow, nphi φ hb, nnat ha, nnat hb, one_pow, inv_one, one_mul]`. Conclude with `mul_le_of_le_one_right (by positivity) (nint m)`.
-/
private theorem E_cong (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r a b : ℕ} (hr : 1 ≤ r) (ha : ¬ l ∣ a) (hb : ¬ l ∣ b)
    (h : a ≡ b [MOD l ^ r]) : ‖E φ k a - E φ k b‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hphi : (a : ZMod l) = (b : ZMod l) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (dvd_pow_self l (by omega)))
  obtain ⟨m, hm⟩ := Nat.modEq_iff_dvd.1 (h.pow k)
  have hmQ : (b : Qbar l) ^ k - (a : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l) := by
    have := congrArg (fun z : ℤ => (z : Qbar l)) hm
    push_cast at this
    exact this
  have nz : ∀ z : Qbar l, ‖z‖ = 1 → z ≠ 0 := fun z hz h => by rw [h, norm_zero] at hz; exact zero_ne_one hz
  have haQ := nz _ (nnat ha)
  have hbQ := nz _ (nnat hb)
  have hpb := nz _ (nphi φ hb)
  have key : E φ k a - E φ k b = (φ (b : ZMod l))⁻¹ * ((a : Qbar l) ^ k)⁻¹ * ((b : Qbar l) ^ k)⁻¹ *
      ((b : Qbar l) ^ k - (a : Qbar l) ^ k) := by
    simp only [E]; rw [hphi]; field_simp
  rw [key, hmQ]
  simp only [norm_mul, norm_inv, norm_pow, nphi φ hb, nnat ha, nnat hb, one_pow, inv_one, one_mul]
  exact mul_le_of_le_one_right (by positivity) (nint m)

/- English proof (translation)
The claim follows from `E_mem c φ k (ndv hr x)`.
-/
private theorem eta_mem (c : Coef l) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r)
    (x : (ZMod (l ^ r))ˣ) : eta φ k r x ∈ c.O := E_mem c φ k (ndv hr x)

/- English proof (translation)
Establish `h` using `E_cong φ k hr (ndv hr (y * x)) (b := (y : ZMod (l ^ r)).val * (x : ZMod (l ^ r)).val) (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim (ndv hr y) (ndv hr x)) (by rw [Units.val_mul, ZMod.val_mul]; exact Nat.mod_modEq _ _)`. Rewrite `h` using `[E_mul]`. Conclude with `h`.
-/
private theorem eta_mul (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) (y x : (ZMod (l ^ r))ˣ) :
    ‖eta φ k r (y * x) - eta φ k r y * eta φ k r x‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have h := E_cong φ k hr (ndv hr (y * x)) (b := (y : ZMod (l ^ r)).val * (x : ZMod (l ^ r)).val)
    (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim (ndv hr y) (ndv hr x))
    (by rw [Units.val_mul, ZMod.val_mul]; exact Nat.mod_modEq _ _)
  rw [E_mul] at h
  exact h

/- English proof (translation)
Use `E_cong φ k hr (ndv (by omega) y) (ndv hr (red l r y)) ?_` and prove the remaining obligations. Rewrite using `[← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`. Simplify using `[ZMod.natCast_val]`.
-/
private theorem eta_red (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) (y : (ZMod (l ^ (r + 1)))ˣ) :
    ‖eta φ k (r + 1) y - eta φ k r (red l r y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  refine E_cong φ k hr (ndv (by omega) y) (ndv hr (red l r y)) ?_
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  simp [ZMod.natCast_val]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {c : Coef l} {Z : Sy Ω l}

/- English proof (translation)
The claim follows from `c.O.sum_mem fun x _ => c.O.mul_mem (eta_mem c φ k hr x) (hZ.int r s hs x)`.
-/
private theorem sp_mem (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) : sp (eta φ k r) (Z r) s ∈ c.O :=
  c.O.sum_mem fun x _ => c.O.mul_mem (eta_mem c φ k hr x) (hZ.int r s hs x)

/- English proof (translation)
Establish `e : sp (eta φ k r) (Z r) s = ∑ y, eta φ k r (red l r y) * Z (r + 1) s y`. Unfold `sp`. Rewrite using `[← Finset.sum_fiberwise (s := Finset.univ) (g := red l r)]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hZ.nrm r s hs x, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations. Rewrite using `[(Finset.mem_filter.1 hy).2]`. Rewrite using `[Cg, e, sp, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_mul, norm_mul]`.

Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ s hs y))).trans (eta_red φ k hr y)`.
-/
private theorem sp_succ (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) : Cg r (sp (eta φ k (r + 1)) (Z (r + 1)) s) (sp (eta φ k r) (Z r) s) := by
  have e : sp (eta φ k r) (Z r) s = ∑ y, eta φ k r (red l r y) * Z (r + 1) s y := by
    unfold sp
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := red l r)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hZ.nrm r s hs x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.1 hy).2]
  rw [Cg, e, sp, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ s hs y))).trans (eta_red φ k hr y)

/- English proof (translation)
Establish `h1 : sp (eta φ k r) (Z r) (s * t) = sp (eta φ k r) (Z r) s + ∑ y, eta φ k r (y * cycMod ℚ Ω l r s) * Z r t y`. Unfold `sp`. Rewrite using `[Finset.sum_congr rfl fun x _ => by rw [hZ.coc r s hs t ht x, mul_add], Finset.sum_add_distrib]`. Use `congr 1`. Conclude with `Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by`.

Rewrite using `[Equiv.coe_mulRight, inv_mul_cancel_right])`. Rewrite using `[h1, add_sub_add_left_eq_sub, sp, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← sub_mul, norm_mul, mul_comm (eta φ k r (cycMod ℚ Ω l r s))]`. Conclude with `(mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ t ht y))).trans (eta_mul φ k hr y _)`.
-/
private theorem sp_mul (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s t : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (ht : t ∈ Ine (F := ℚ) A) :
    ‖sp (eta φ k r) (Z r) (s * t) - (sp (eta φ k r) (Z r) s +
      eta φ k r (cycMod ℚ Ω l r s) * sp (eta φ k r) (Z r) t)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have h1 : sp (eta φ k r) (Z r) (s * t) = sp (eta φ k r) (Z r) s +
      ∑ y, eta φ k r (y * cycMod ℚ Ω l r s) * Z r t y := by
    unfold sp
    rw [Finset.sum_congr rfl fun x _ => by rw [hZ.coc r s hs t ht x, mul_add], Finset.sum_add_distrib]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by
      rw [Equiv.coe_mulRight, inv_mul_cancel_right])
  rw [h1, add_sub_add_left_eq_sub, sp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_
  rw [← mul_assoc, ← sub_mul, norm_mul, mul_comm (eta φ k r (cycMod ℚ Ω l r s))]
  exact (mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ t ht y))).trans (eta_mul φ k hr y _)

/- English proof (translation)
Simplify using `only [sp, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[hZ.coc r h hh m hm x, hc, inv_one, mul_one, mul_add]`.
-/
private theorem sp_triv (hZ : IwI c A Z) {r : ℕ} (η : (ZMod (l ^ r))ˣ → Qbar l) {h m : G ℚ Ω}
    (hh : h ∈ Ine (F := ℚ) A) (hm : m ∈ Ine (F := ℚ) A) (hc : cycMod ℚ Ω l r h = 1) :
    sp η (Z r) (h * m) = sp η (Z r) h + sp η (Z r) m := by
  simp only [sp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hZ.coc r h hh m hm x, hc, inv_one, mul_one, mul_add]

/- English proof (translation)
Simplify using `only [map_mul, map_inv]`. Rewrite using `[mul_right_comm (f x), mul_inv_cancel_right, mul_inv_cancel]`.
-/
private theorem comm_triv {M G' : Type*} [CommGroup M] [Group G'] (f : G' →* M) (x y : G') :
    f (x * y * x⁻¹ * y⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [mul_right_comm (f x), mul_inv_cancel_right, mul_inv_cancel]

/- English proof (translation)
Establish `hl2` using `(Fact.out : l.Prime).two_le`. Establish `hlt : 1 + l < l ^ r`. Establish `h1 : l ^ 2 ≤ l ^ r` using `Nat.pow_le_pow_right (by omega) hr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hv : ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = 1 + l`.

Establish `: ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = PadicInt.toZModPow r (cycZ ℚ Ω l t : ℤ_[l])` using `rfl`. Rewrite using `[this, ht, map_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]`. Simplify using `only [eta, hv]`. Establish `h1 : ((1 + l : ℕ) : ZMod l) = 1` using `by push_cast; simp`. Rewrite using `[h1, map_one, inv_one, one_mul]`.
-/
private theorem eta_gam (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) {t : G ℚ Ω}
    (ht : (cycZ ℚ Ω l t : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l])) :
    eta φ k r (cycMod ℚ Ω l r t) = (((1 + l : ℕ) : Qbar l) ^ k)⁻¹ := by
  have hl2 := (Fact.out : l.Prime).two_le
  have hlt : 1 + l < l ^ r := by
    have h1 : l ^ 2 ≤ l ^ r := Nat.pow_le_pow_right (by omega) hr
    nlinarith
  have hv : ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = 1 + l := by
    have : ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = PadicInt.toZModPow r (cycZ ℚ Ω l t : ℤ_[l]) := rfl
    rw [this, ht, map_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  simp only [eta, hv]
  have h1 : ((1 + l : ℕ) : ZMod l) = 1 := by push_cast; simp
  rw [h1, map_one, inv_one, one_mul]

/- English proof (translation)
Establish `hl2` using `(Fact.out : l.Prime).two_le`. Establish `h1 : 1 < (1 + l) ^ k` using `Nat.one_lt_pow (by omega) (by omega)`. Take `⟨e, m, hm, hN⟩` from `Nat.exists_eq_pow_mul_and_not_dvd (n := (1 + l) ^ k - 1) (by omega) l (by omega)`. Establish `hN' : (1 + l) ^ k = l ^ e * m + 1` using `by omega`. Establish `hQ : ((1 + l : ℕ) : Qbar l) ^ k = (l : Qbar l) ^ e * m + 1` using `by exact_mod_cast congrArg (Nat.cast (R := Qbar l)) hN'`.

Establish `hm0 : (m : Qbar l) ≠ 0` using `fun h => by have := nnat hm; rw [h, norm_zero] at this; exact zero_ne_one this`. Establish `hb0 : ((1 + l : ℕ) : Qbar l) ^ k ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))`. Use `⟨e, -(((1 + l : ℕ) : Qbar l) ^ k * (m : Qbar l)⁻¹), c.O.neg_mem (c.O.mul_mem (c.O.pow_mem (natCast_mem c.O _) k) (invO c (natCast_mem c.O m) (nnat hm))), ?_⟩` and prove the remaining obligations. Generalize the expression as in `((1 + l : ℕ) : Qbar l) ^ k = B at hQ hb0`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[hQ]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem split_pow (c : Coef l) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (c₂ : ℕ) (v : Qbar l), v ∈ c.O ∧ ((l : ℕ) : Qbar l) ^ c₂ = ((((1 + l : ℕ) : Qbar l) ^ k)⁻¹ - 1) * v := by
  have hl2 := (Fact.out : l.Prime).two_le
  have h1 : 1 < (1 + l) ^ k := Nat.one_lt_pow (by omega) (by omega)
  obtain ⟨e, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := (1 + l) ^ k - 1) (by omega) l (by omega)
  have hN' : (1 + l) ^ k = l ^ e * m + 1 := by omega
  have hQ : ((1 + l : ℕ) : Qbar l) ^ k = (l : Qbar l) ^ e * m + 1 := by exact_mod_cast congrArg (Nat.cast (R := Qbar l)) hN'
  have hm0 : (m : Qbar l) ≠ 0 := fun h => by have := nnat hm; rw [h, norm_zero] at this; exact zero_ne_one this
  have hb0 : ((1 + l : ℕ) : Qbar l) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  refine ⟨e, -(((1 + l : ℕ) : Qbar l) ^ k * (m : Qbar l)⁻¹),
    c.O.neg_mem (c.O.mul_mem (c.O.pow_mem (natCast_mem c.O _) k) (invO c (natCast_mem c.O m) (nnat hm))), ?_⟩
  generalize ((1 + l : ℕ) : Qbar l) ^ k = B at hQ hb0
  field_simp
  rw [hQ]; ring

end UpperTheory.Kd.C7.CoboundaryRoots

open UpperTheory.Kd.C7.CoboundaryRoots in
/- English proof (translation)
Introduce `l _ hl2 Ω _ _ _ A hA c Z hZ φ k hk hsp`. Establish `hu : IsUnit ((1 + l : ℕ) : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Simplify using the standard rewrite rules. Take `⟨t, htI, ht⟩` from `(pFrobEx l hl2 Ω A hA).2.2 hu.unit`.

Establish `ht' : (cycZ ℚ Ω l t : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l])` using `by rw [ht]; rfl`. Take `⟨z, hzO, hz⟩` from `exists_limit_coef l c Unit (fun n _ => sp (eta φ k (n + 1)) (Z (n + 1)) t) (fun n _ => sp_mem hZ φ k (by omega) htI) (fun n _ => (sp_succ hZ φ k (r := n + 1) (by omega) htI).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega)))`. Take `⟨c₂, v, hvO, hv⟩` from `split_pow c hk`. Use `⟨c₂, v * z (), c.O.mul_mem hvO (hzO ()), fun s hs n => ?_⟩` and prove the remaining obligations. Take `⟨r₀, hr₀⟩` from `hsp n`.

Use `⟨max r₀ (n + 2), fun r hr => ?_⟩` and prove the remaining obligations. Establish `hr0 : r₀ ≤ r` using `le_trans (le_max_left _ _) hr`. Establish `hr2 : n + 2 ≤ r` using `le_trans (le_max_right _ _) hr`. Take `⟨q, rfl⟩ : ∃ q, r = q + 1` from `⟨r - 1, by omega⟩`. Establish `hr1 : 1 ≤ q + 1` using `by omega`.

Establish `hlim : ‖z () - sp (eta φ k (q + 1)) (Z (q + 1)) t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖` using `(hz q ()).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega))`. Establish `hhI : t * s * t⁻¹ * s⁻¹ ∈ Ine (F` using `ℚ) A := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htI hs) (Subgroup.inv_mem _ htI)) (Subgroup.inv_mem _ hs)`. Establish `hsmall` using `hr₀ _ hr0 _ hhI (comm_triv _ t s)`. Establish `hts : t * s = (t * s * t⁻¹ * s⁻¹) * (s * t)` using `by group`. Establish `hB` using `sp_triv hZ (eta φ k (q + 1)) hhI (Subgroup.mul_mem _ hs htI) (comm_triv _ t s)`.

Rewrite `hB` using `[← hts]`. Establish `hAa` using `sp_mul hZ φ k hr1 htI hs`. Rewrite `hAa` using `[eta_gam φ k (by omega) ht']`. Establish `hCa` using `sp_mul hZ φ k hr1 hs htI`. Establish `hrle : ‖((l : ℕ) : Qbar l) ^ (q + 1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖` using `GlobalTheory.Ord2.norm_l_pow_anti (by omega)`.

Establish `hρ : ‖eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) - 1‖ ≤ 1` using `nO c (c.O.sub_mem (eta_mem c φ k hr1 _) c.O.one_mem)`. Rewrite `hsmall` using `[Cg, sub_zero]`. Rewrite using `[Cg, hv]`. Generalize the expression as in `sp (eta φ k (q + 1)) (Z (q + 1)) (t * s * t⁻¹ * s⁻¹) = fh at hsmall hB`. Generalize the expression as in `sp (eta φ k (q + 1)) (Z (q + 1)) (t * s) = fts at hB hAa`.

Generalize the expression as in `sp (eta φ k (q + 1)) (Z (q + 1)) (s * t) = fst at hB hCa`. Generalize the expression as in `sp (eta φ k (q + 1)) (Z (q + 1)) s = X at hAa hCa ⊢`. Generalize the expression as in `sp (eta φ k (q + 1)) (Z (q + 1)) t = T at hAa hCa hlim`. Generalize the expression as in `eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) = ρ at hCa hρ ⊢`. Generalize the expression as in `(((1 + l : ℕ) : Qbar l) ^ k)⁻¹ = β at hAa ⊢`.

Establish `e : (β - 1) * v * X - (ρ - 1) * (v * z ()) = v * (((fh - (fts - (T + β * X))) + (fst - (X + ρ * T))) - (ρ - 1) * (z () - T))`. Rewrite using `[hB]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul]`. Use `(mul_le_of_le_one_left (norm_nonneg _) (nO c hvO)).trans ((nsub _ _).trans (max_le ?_ ?_))` and prove the remaining obligations.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((nsub _ _).trans (max_le hsmall (hAa.trans hrle))) (hCa.trans hrle))`. Rewrite using `[norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) hρ).trans hlim`.
-/
theorem UpperTheory.Kd.C7.pCob :
    UpperTheory.Kd.C7.SCob := by
  intro l _ hl2 Ω _ _ _ A hA c Z hZ φ k hk hsp
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, htI, ht⟩ := (pFrobEx l hl2 Ω A hA).2.2 hu.unit
  have ht' : (cycZ ℚ Ω l t : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by rw [ht]; rfl
  obtain ⟨z, hzO, hz⟩ := exists_limit_coef l c Unit (fun n _ => sp (eta φ k (n + 1)) (Z (n + 1)) t)
    (fun n _ => sp_mem hZ φ k (by omega) htI)
    (fun n _ => (sp_succ hZ φ k (r := n + 1) (by omega) htI).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega)))
  obtain ⟨c₂, v, hvO, hv⟩ := split_pow c hk
  refine ⟨c₂, v * z (), c.O.mul_mem hvO (hzO ()), fun s hs n => ?_⟩
  obtain ⟨r₀, hr₀⟩ := hsp n
  refine ⟨max r₀ (n + 2), fun r hr => ?_⟩
  have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : n + 2 ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hr1 : 1 ≤ q + 1 := by omega
  have hlim : ‖z () - sp (eta φ k (q + 1)) (Z (q + 1)) t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hz q ()).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega))
  have hhI : t * s * t⁻¹ * s⁻¹ ∈ Ine (F := ℚ) A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htI hs) (Subgroup.inv_mem _ htI)) (Subgroup.inv_mem _ hs)
  have hsmall := hr₀ _ hr0 _ hhI (comm_triv _ t s)
  have hts : t * s = (t * s * t⁻¹ * s⁻¹) * (s * t) := by group
  have hB := sp_triv hZ (eta φ k (q + 1)) hhI (Subgroup.mul_mem _ hs htI) (comm_triv _ t s)
  rw [← hts] at hB
  have hAa := sp_mul hZ φ k hr1 htI hs
  rw [eta_gam φ k (by omega) ht'] at hAa
  have hCa := sp_mul hZ φ k hr1 hs htI
  have hrle : ‖((l : ℕ) : Qbar l) ^ (q + 1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := GlobalTheory.Ord2.norm_l_pow_anti (by omega)
  have hρ : ‖eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) - 1‖ ≤ 1 :=
    nO c (c.O.sub_mem (eta_mem c φ k hr1 _) c.O.one_mem)
  rw [Cg, sub_zero] at hsmall
  rw [Cg, hv]
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (t * s * t⁻¹ * s⁻¹) = fh at hsmall hB
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (t * s) = fts at hB hAa
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (s * t) = fst at hB hCa
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) s = X at hAa hCa ⊢
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) t = T at hAa hCa hlim
  generalize eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) = ρ at hCa hρ ⊢
  generalize (((1 + l : ℕ) : Qbar l) ^ k)⁻¹ = β at hAa ⊢
  have e : (β - 1) * v * X - (ρ - 1) * (v * z ()) =
      v * (((fh - (fts - (T + β * X))) + (fst - (X + ρ * T))) - (ρ - 1) * (z () - T)) := by
    rw [hB]; ring
  rw [e, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (nO c hvO)).trans ((nsub _ _).trans (max_le ?_ ?_))
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((nsub _ _).trans (max_le hsmall (hAa.trans hrle))) (hCa.trans hrle))
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hρ).trans hlim
