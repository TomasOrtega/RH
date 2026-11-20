import Formalism.FormalGroupWitt.FormalGroupWittProofs.FunctionalEquationHomVector
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne
import Formalism.FormalGroupWitt.FormalGroupWittProofs.ShiftFE
import Formalism.FormalGroupWitt.FormalGroupWittProofs.FrobSqV
import Formalism.FormalGroupWitt.FormalGroupWittProofs.CongrV

noncomputable section

namespace Formalism.FG.HeightVAux

open MvPowerSeries Formalism.G Formalism.LT

section Rename

variable {K : Type*} [Field K] {l m : ℕ} [NeZero m]

/- English proof (translation)
Use `set e : ZMod m ↪ ZMod m := (Equiv.subRight (1 : ZMod m)).toEmbedding with he`. Establish `hs : ∀ a : ZMod m, e a = a - 1` using `fun a => by simp [he]`. Establish `hX : (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) = X ∘ ⇑e`. Use function extensionality and compare the values at `k`. Simplify using `[hs]`.

Rewrite using `[hX, ← rename_eq_subst]`. Use extensionality with `n`. Take `⟨x, rfl⟩ : ∃ x, Finsupp.embDomain e x = n` from `⟨n.comapDomain e e.injective.injOn, Finsupp.embDomain_comapDomain (by`. Introduce `a _; exact ⟨a + 1, by simp [hs]⟩)⟩`. Rewrite using `[coeff_embDomain_rename]`.

Distinguish the cases in `hA : ∃ t : ℕ, x = Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)`. Take `⟨t, rfl⟩` from `hA`. Rewrite using `[Finsupp.embDomain_single, hs, ShiftFEAux.coeff_shiftLog_single hl]`. Establish `: j - (t : ZMod m) - 1 = j - 1 - (t : ZMod m)` using `by ring`. Rewrite using `[this, ShiftFEAux.coeff_shiftLog_single hl]`.

Use `push Not at hA`. Rewrite using `[ShiftFEAux.coeff_shiftLog_zero j x hA, ShiftFEAux.coeff_shiftLog_zero]`. Introduce `t ht`. Apply `hA t` to reduce the goal to its premises. Establish `: Finsupp.single (j - 1 - (t : ZMod m)) ((l ^ 2) ^ t) = Finsupp.embDomain e (Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t))`.

Rewrite using `[Finsupp.embDomain_single, hs]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `ht` using `[this]`. Conclude with `Finsupp.embDomain_inj.mp ht`.
-/
theorem subst_shift_shiftLog (hl : 2 ≤ l) (j : ZMod m) :
    subst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) (shiftLog K l m j) =
      shiftLog K l m (j - 1) := by
  classical
  set e : ZMod m ↪ ZMod m := (Equiv.subRight (1 : ZMod m)).toEmbedding with he
  have hs : ∀ a : ZMod m, e a = a - 1 := fun a => by simp [he]
  have hX : (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) K)) = X ∘ ⇑e := by
    funext k; simp [hs]
  rw [hX, ← rename_eq_subst]
  ext n
  obtain ⟨x, rfl⟩ : ∃ x, Finsupp.embDomain e x = n :=
    ⟨n.comapDomain e e.injective.injOn, Finsupp.embDomain_comapDomain (by
      intro a _; exact ⟨a + 1, by simp [hs]⟩)⟩
  rw [coeff_embDomain_rename]
  by_cases hA : ∃ t : ℕ, x = Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)
  · obtain ⟨t, rfl⟩ := hA
    rw [Finsupp.embDomain_single, hs, ShiftFEAux.coeff_shiftLog_single hl]
    have : j - (t : ZMod m) - 1 = j - 1 - (t : ZMod m) := by ring
    rw [this, ShiftFEAux.coeff_shiftLog_single hl]
  · push Not at hA
    rw [ShiftFEAux.coeff_shiftLog_zero j x hA, ShiftFEAux.coeff_shiftLog_zero]
    intro t ht
    apply hA t
    have : Finsupp.single (j - 1 - (t : ZMod m)) ((l ^ 2) ^ t) =
        Finsupp.embDomain e (Finsupp.single (j - (t : ZMod m)) ((l ^ 2) ^ t)) := by
      rw [Finsupp.embDomain_single, hs]; congr 1; ring
    rw [this] at ht
    exact Finsupp.embDomain_inj.mp ht

end Rename

section Subst

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [DecidableEq ι] {τ : Type*}

/- English proof (translation)
The claim follows from `hasSubst_of_constantCoeff_zero ha`.
-/
theorem hasSubst0 {σ : Type*} [Finite σ] (a : σ → MvPowerSeries τ R)
    (ha : ∀ i, constantCoeff (a i) = 0) : HasSubst a :=
  hasSubst_of_constantCoeff_zero ha

/- English proof (translation)
The claim follows from `hasSubst0 _ (fun _ => constantCoeff_X _)`.
-/
theorem hasSubst_vX : HasSubst (fun i : ι => (vX i : MvPowerSeries (Fin 2 × ι) R)) :=
  hasSubst0 _ (fun _ => constantCoeff_X _)

/- English proof (translation)
The claim follows from `hasSubst0 _ (fun _ => constantCoeff_X _)`.
-/
theorem hasSubst_vY : HasSubst (fun i : ι => (vY i : MvPowerSeries (Fin 2 × ι) R)) :=
  hasSubst0 _ (fun _ => constantCoeff_X _)

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero hasSubst_vX (fun _ => constantCoeff_X _) hg`.
-/
theorem constantCoeff_atXv {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atXv g) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_vX (fun _ => constantCoeff_X _) hg

/- English proof (translation)
The claim follows from `constantCoeff_subst_eq_zero hasSubst_vY (fun _ => constantCoeff_X _) hg`.
-/
theorem constantCoeff_atYv {g : MvPowerSeries ι R} (hg : constantCoeff g = 0) :
    constantCoeff (atYv g) = 0 :=
  constantCoeff_subst_eq_zero hasSubst_vY (fun _ => constantCoeff_X _) hg

/- English proof (translation)
Unfold `atXv`. Rewrite using `[subst_comp_subst_apply hasSubst_vX hG]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `subst_X hG _`.
-/
theorem subst_atXv (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atXv g) = subst (fun i => G (0, i)) g := by
  unfold atXv
  rw [subst_comp_subst_apply hasSubst_vX hG]
  congr 1
  funext i
  exact subst_X hG _

/- English proof (translation)
Unfold `atYv`. Rewrite using `[subst_comp_subst_apply hasSubst_vY hG]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `subst_X hG _`.
-/
theorem subst_atYv (G : Fin 2 × ι → MvPowerSeries τ R) (hG : HasSubst G)
    (g : MvPowerSeries ι R) : subst G (atYv g) = subst (fun i => G (1, i)) g := by
  unfold atYv
  rw [subst_comp_subst_apply hasSubst_vY hG]
  congr 1
  funext i
  exact subst_X hG _

/- English proof (translation)
Unfold `atXv`. Rewrite using `[subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vX]`.
-/
theorem atXv_subst (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atXv (subst h g) = subst (fun i => atXv (h i)) g := by
  unfold atXv
  rw [subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vX]

/- English proof (translation)
Unfold `atYv`. Rewrite using `[subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vY]`.
-/
theorem atYv_subst (h : ι → MvPowerSeries ι R) (hh : ∀ i, constantCoeff (h i) = 0)
    (g : MvPowerSeries ι R) : atYv (subst h g) = subst (fun i => atYv (h i)) g := by
  unfold atYv
  rw [subst_comp_subst_apply (hasSubst0 h hh) hasSubst_vY]

/- English proof (translation)
Unfold `atXv`. Rewrite using `[map_subst hasSubst_vX]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_X φ _`.
-/
theorem map_atXv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atXv g) = atXv (map φ g) := by
  unfold atXv
  rw [map_subst hasSubst_vX]
  congr 1
  funext i
  exact map_X φ _

/- English proof (translation)
Unfold `atYv`. Rewrite using `[map_subst hasSubst_vY]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `map_X φ _`.
-/
theorem map_atYv {S : Type*} [CommRing S] (φ : R →+* S) (g : MvPowerSeries ι R) :
    map φ (atYv g) = atYv (map φ g) := by
  unfold atYv
  rw [map_subst hasSubst_vY]
  congr 1
  funext i
  exact map_X φ _

end Subst

section Padic

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Introduce `a b hab`. Use extensionality with `n`. Use `congrArg (coeff n) hab` as an intermediate fact. Rewrite `this` using `[coeff_map, coeff_map]`. Conclude with `Subtype.ext this`.
-/
theorem coe_map_injective {σ : Type*} :
    Function.Injective (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) :
      MvPowerSeries σ ℤ_[l] → MvPowerSeries σ ℚ_[l]) := by
  intro a b hab
  ext n
  have := congrArg (coeff n) hab
  rw [coeff_map, coeff_map] at this
  exact Subtype.ext this

/- English proof (translation)
Rewrite `hx` using `[constantCoeff_map]`. Conclude with `Subtype.ext hx`.
-/
theorem constantCoeff_of_map {σ : Type*} (x : MvPowerSeries σ ℤ_[l])
    (hx : constantCoeff (map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x) = 0) :
    constantCoeff x = 0 := by
  rw [constantCoeff_map] at hx
  exact Subtype.ext hx

def liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) : MvPowerSeries σ ℤ_[l] :=
  fun n => ⟨coeff n g, hg n⟩

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_map]`. Both sides reduce to the same expression.
-/
theorem map_liftZ {σ : Type*} (g : MvPowerSeries σ ℚ_[l]) (hg : IntegralMv g) :
    map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (liftZ g hg) = g := by
  ext n
  rw [coeff_map]
  rfl

/- English proof (translation)
The claim follows from `(PadicInt.norm_lt_one_iff_dvd x).mp (lt_of_le_of_lt hx Padic.norm_p_lt_one)`.
-/
theorem dvd_of_norm_le {x : ℤ_[l]}
    (hx : ‖(PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) x‖ ≤ ‖((l : ℕ) : ℚ_[l])‖) :
    (l : ℤ_[l]) ∣ x :=
  (PadicInt.norm_lt_one_iff_dvd x).mp (lt_of_le_of_lt hx Padic.norm_p_lt_one)

/- English proof (translation)
Rewrite using `[← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`.
-/
theorem toZMod_eq_zero_iff (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ (l : ℤ_[l]) ∣ x := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton]

end Padic

section Main

open PadicInt in
/- English proof (translation)
Introduce `l _ m _ F hF`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hl2 : 2 ≤ l` using `hlp.two_le`. Establish `hq : l ^ 2 ≠ 0` using `pow_ne_zero 2 hlp.ne_zero`. Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `by exact_mod_cast hlp.ne_zero`.

Take `⟨hf, hfeq⟩` from `Formalism.FG.shift_functional_equation.{0} ℚ_[l] l hlp m (RingHom.id ℚ_[l])`. Establish `hS` using `Formalism.FG.frobenius_lift_padic_square l`. Establish `hM : IntegralMat (shiftMat ℚ_[l] m)`. Apply the tactic sequence `intro j k; unfold shiftMat; split_ifs <;> simp`. Establish `hXI : ∀ j : ZMod m, IntegralMv (X j : MvPowerSeries (ZMod m) ℚ_[l])`.

Apply the tactic sequence `intro j d; rw [coeff_X]; split_ifs <;> simp`. Establish `hfE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m) (shiftLog ℚ_[l] l m)`. Introduce `j`. Rewrite using `[hfeq j]`. Conclude with `hXI j`.

Establish `hsum : ∀ j : ZMod m, ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) = MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1))`. Introduce `j`. Simplify using `[shiftMat]`. Establish `hexp : ∀ j : ZMod m, MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) = (l : ℚ_[l]) • (shiftLog ℚ_[l] l m j - X j)`. Introduce `j`.

Establish `h1` using `hfeq j`. Rewrite `h1` using `[hsum j]`. Rewrite using `[← h1, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hl0, one_smul]`. Establish `hgE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m) (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j)`. Introduce `j`.

Establish `: (l : ℚ_[l]) • shiftLog ℚ_[l] l m j - ((l : ℕ) : ℚ_[l])⁻¹ • ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k)) = (l : ℚ_[l]) • (X j : MvPowerSeries (ZMod m) ℚ_[l])`. Establish `h2 : ∀ k, MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k) = (l : ℚ_[l]) • MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)`. Introduce `k`. Simplify using the standard rewrite rules. Establish `h3 : ∑ k, shiftMat ℚ_[l] m j k • (l : ℚ_[l]) • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) = (l : ℚ_[l]) • ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k))`.

Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => smul_comm _ _ _`. Simplify using `only [h2, map_smul]`. Rewrite using `[h3, hsum j, hexp j]`. Rewrite using `[smul_smul ((l : ℚ_[l])⁻¹), inv_mul_cancel₀ hl0, one_smul, ← smul_sub, sub_sub_cancel]`.

Rewrite using `[this]`. Introduce `d`. Rewrite using `[coeff_smul, norm_mul]`. Conclude with `mul_le_one₀ Padic.norm_p_lt_one.le (norm_nonneg _) (hXI j d)`. Establish `hg0 : ∀ j : ZMod m, constantCoeff ((l : ℚ_[l]) • shiftLog ℚ_[l] l m j) = 0`.

Introduce `j`. Rewrite using `[smul_eq_C_mul, map_mul, hf.1 j, mul_zero]`. Take `⟨h, hh0, hhI, hh⟩` from `Formalism.FG.functional_equation_hom_vector.{0, 0, 0} ℚ_[l] l (l ^ 2) hq (RingHom.id ℚ_[l]) hS (ZMod m) (shiftMat ℚ_[l] m) hM (shiftLog ℚ_[l] l m) hf hfE (ZMod m) (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) hg0 hgE`. Use `set e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l] := fun i => liftZ (h i) (hhI i) with he_def`. Establish `he : ∀ i, map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e i) = h i` using `fun i => map_liftZ (h i) (hhI i)`.

Establish `he0 : ∀ i, constantCoeff (e i) = 0` using `fun i => constantCoeff_of_map _ (by rw [he i]; exact hh0 i)`. Establish `hF0 : ∀ i, constantCoeff (F i) = 0` using `fun i => constantCoeff_of_map _ (hF.1 i)`. Use `set FK : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] := fun i => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (F i) with hFK`. Use `set EK : Fin 2 × ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] := fun x => if x.1 = 0 then atXv (h x.2) else atYv (h x.2) with hEK`. Establish `hFKs : HasSubst FK` using `hasSubst0 FK hF.1`.

Establish `hhs : HasSubst h` using `hasSubst0 h hh0`. Establish `hEK0 : ∀ x, constantCoeff (EK x) = 0`. Introduce `x`. Simplify using `only [hEK]`. Use `split_ifs`.

Conclude with `constantCoeff_atXv (hh0 _)`. Conclude with `constantCoeff_atYv (hh0 _)`. Establish `hEKs : HasSubst EK` using `hasSubst0 EK hEK0`. Establish `hkey : (fun i => subst FK (h i)) = (fun i => subst EK (FK i))`. Use `Formalism.FG.subst_injective_vector.{0, 0, 0} ℚ_[l] (ZMod m) (Fin 2 × ZMod m) (shiftLog ℚ_[l] l m) _ _ hf (fun i => constantCoeff_subst_eq_zero hFKs hF.1 (hh0 i)) (fun i => constantCoeff_subst_eq_zero hEKs hEK0 (hF.1 i)) (fun j => ?_)` and prove the remaining obligations.

Rewrite using `[← subst_comp_subst_apply hhs hFKs, hh j, subst_smul hFKs, hF.2.2 j, ← subst_comp_subst_apply hFKs hEKs, hF.2.2 j, subst_add hEKs, subst_atXv EK hEKs, subst_atYv EK hEKs]`. Establish `hx : (fun i => EK (0, i)) = fun i => atXv (h i)`. Use function extensionality and compare the values at `i`. Simplify using `[hEK]`. Establish `hy : (fun i => EK (1, i)) = fun i => atYv (h i)`.

Use function extensionality and compare the values at `i`. Simplify using `[hEK]`. Rewrite using `[hx, hy, ← atXv_subst h hh0, ← atYv_subst h hh0, hh j, smul_add]`. Unfold `atXv atYv`. Rewrite using `[subst_smul hasSubst_vX, subst_smul hasSubst_vY]`.

Establish `hFs : HasSubst F` using `hasSubst0 F hF0`. Establish `hE0 : ∀ x : Fin 2 × ZMod m, constantCoeff ((fun x : Fin 2 × ZMod m => if x.1 = 0 then atXv (e x.2) else atYv (e x.2)) x) = 0`. Introduce `x`. Simplify using `only`. Use `split_ifs`.

Conclude with `constantCoeff_atXv (he0 _)`. Conclude with `constantCoeff_atYv (he0 _)`. Establish `hHom : IsHomV F F e`. Use `⟨he0, fun i => ?_⟩` and prove the remaining obligations. Apply `coe_map_injective` to reduce the goal to its premises.

Rewrite using `[map_subst hFs, map_subst (hasSubst0 _ hE0), he i]`. Use `congrFun hkey i` as an intermediate fact. Rewrite using `[this]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Simplify using `only [hEK]`. Use `split_ifs`. Rewrite using `[map_atXv, he]`. Rewrite using `[map_atYv, he]`. Establish `hfe : (fun k => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e k)) = h` using `funext he`.

Use `set β : ZMod m → MvPowerSeries (ZMod m) ℚ_[l] := fun k => X (k - 1) ^ (l ^ 2) with hβ`. Establish `hβ0 : ∀ k, constantCoeff (β k) = 0`. Introduce `k`. Simplify using `[hβ, hlp.ne_zero]`. Establish `hβI : ∀ k, IntegralMv (β k)`.

Apply the tactic sequence `intro k d; simp only [hβ]; rw [coeff_X_pow]; split_ifs <;> simp`. Establish `hρs : HasSubst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) ℚ_[l]))` using `hasSubst0 _ (fun _ => constantCoeff_X _)`. Establish `hβf : ∀ j, subst β (shiftLog ℚ_[l] l m j) = MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1))`. Introduce `j`. Establish `: β = fun k => MvPowerSeries.expand (l ^ 2) hq (X (k - 1))`.

Use function extensionality and compare the values at `k`. Simplify using `[hβ]`. Rewrite using `[this, ← expand_subst _ _ hρs, subst_shift_shiftLog hl2]`. Establish `hdiv` using `(hC ℚ_[l] l (l ^ 2) hq (RingHom.id _) hS (ZMod m) (shiftMat ℚ_[l] m) hM (shiftLog ℚ_[l] l m) hf hfE (ZMod m) h β hh0 hβ0 hhI hβI 1 le_rfl).mpr (by`. Introduce `j d`.

Rewrite using `[hh j, hβf j, hexp j, ← smul_sub, sub_sub_cancel, pow_one, coeff_smul, norm_mul]`. Conclude with `mul_le_of_le_one_right (norm_nonneg _) (hXI j d))`. Establish `hcongr : ∀ j n, (l : ℤ_[l]) ∣ coeff n (e j - X (j - 1) ^ (l ^ 2))`. Introduce `j n`. Apply `dvd_of_norm_le` to reduce the goal to its premises.

Establish `hmap : h j - β j = map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e j - X (j - 1) ^ (l ^ 2))`. Rewrite using `[map_sub, map_pow, map_X, he j]`. Use `hdiv j n` as an intermediate fact. Rewrite `this` using `[hmap, coeff_map, pow_one]`. Conclude with `this`.

Establish `hred : ∀ j, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j) = X (j - 1) ^ (l ^ 2)`. Introduce `j`. Establish `h0 : map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j - X (j - 1) ^ (l ^ 2)) = 0`. Use extensionality with `n`. Rewrite using `[coeff_map, map_zero, toZMod_eq_zero_iff]`.

Conclude with `hcongr j n`. Rewrite `h0` using `[map_sub, map_pow, map_X, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hit : ∀ n : ℕ, (∀ i, constantCoeff (iterV e n i) = 0) ∧ ∀ i, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (iterV e n i) = X (i - (n : ZMod m)) ^ ((l ^ 2) ^ n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Simplify using `[iterV]`. Simplify using `[iterV, map_X]`. Consider the case `succ n ih`.

Establish `hsucc : ∀ i, iterV e (n + 1) i = subst (iterV e n) (e i)`. Introduce `i`. Simplify using `only [iterV]`. Rewrite using `[Function.iterate_succ_apply']`. Establish `hs1 : HasSubst (iterV e n)` using `hasSubst0 _ ih.1`.

Use `⟨fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hsucc]`. Conclude with `constantCoeff_subst_eq_zero hs1 ih.1 (he0 i)`. Rewrite using `[hsucc, map_subst hs1, hred i, subst_pow (hs1.map _), subst_X (hs1.map _), ih.2, ← pow_mul, ← pow_succ]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨e, hHom, fun j => by rw [hfe]; exact hh j, hcongr, fun j n => ?_⟩` and prove the remaining obligations. Rewrite using `[← toZMod_eq_zero_iff, ← coeff_map, map_sub, (hit m).2 j, ZMod.natCast_self, sub_zero, ← pow_mul, map_pow, map_X, sub_self, map_zero]`.
-/
theorem main (hC : Formalism.FG.FunEqCongrV.{0, 0, 0}) : Formalism.FG.ShiftHeight := by
  intro l _ m _ F hF
  have hlp : l.Prime := Fact.out
  have hl2 : 2 ≤ l := hlp.two_le
  have hq : l ^ 2 ≠ 0 := pow_ne_zero 2 hlp.ne_zero
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast hlp.ne_zero
  obtain ⟨hf, hfeq⟩ := Formalism.FG.shift_functional_equation.{0} ℚ_[l] l hlp m (RingHom.id ℚ_[l])
  have hS := Formalism.FG.frobenius_lift_padic_square l
  have hM : IntegralMat (shiftMat ℚ_[l] m) := by
    intro j k; unfold shiftMat; split_ifs <;> simp
  have hXI : ∀ j : ZMod m, IntegralMv (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
    intro j d; rw [coeff_X]; split_ifs <;> simp
  have hfE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (shiftLog ℚ_[l] l m) := by
    intro j; rw [hfeq j]; exact hXI j

  have hsum : ∀ j : ZMod m, ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    simp [shiftMat]
  have hexp : ∀ j : ZMod m, MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) =
      (l : ℚ_[l]) • (shiftLog ℚ_[l] l m j - X j) := by
    intro j
    have h1 := hfeq j
    rw [hsum j] at h1
    rw [← h1, sub_sub_cancel, smul_smul, mul_inv_cancel₀ hl0, one_smul]

  have hgE : IsFunEqTypeV l (l ^ 2) hq (RingHom.id ℚ_[l]) (shiftMat ℚ_[l] m)
      (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) := by
    intro j
    have : (l : ℚ_[l]) • shiftLog ℚ_[l] l m j - ((l : ℕ) : ℚ_[l])⁻¹ • ∑ k, shiftMat ℚ_[l] m j k •
        MvPowerSeries.expand (l ^ 2) hq
          (MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k)) =
        (l : ℚ_[l]) • (X j : MvPowerSeries (ZMod m) ℚ_[l]) := by
      have h2 : ∀ k, MvPowerSeries.map (RingHom.id ℚ_[l]) ((l : ℚ_[l]) • shiftLog ℚ_[l] l m k) =
          (l : ℚ_[l]) • MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k) := by
        intro k; simp
      have h3 : ∑ k, shiftMat ℚ_[l] m j k • (l : ℚ_[l]) • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) =
          (l : ℚ_[l]) • ∑ k, shiftMat ℚ_[l] m j k • MvPowerSeries.expand (l ^ 2) hq
            (MvPowerSeries.map (RingHom.id ℚ_[l]) (shiftLog ℚ_[l] l m k)) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
      simp only [h2, map_smul]
      rw [h3, hsum j, hexp j]
      rw [smul_smul ((l : ℚ_[l])⁻¹), inv_mul_cancel₀ hl0, one_smul, ← smul_sub, sub_sub_cancel]
    rw [this]
    intro d
    rw [coeff_smul, norm_mul]
    exact mul_le_one₀ Padic.norm_p_lt_one.le (norm_nonneg _) (hXI j d)
  have hg0 : ∀ j : ZMod m, constantCoeff ((l : ℚ_[l]) • shiftLog ℚ_[l] l m j) = 0 := by
    intro j
    rw [smul_eq_C_mul, map_mul, hf.1 j, mul_zero]
  obtain ⟨h, hh0, hhI, hh⟩ := Formalism.FG.functional_equation_hom_vector.{0, 0, 0} ℚ_[l] l (l ^ 2) hq
    (RingHom.id ℚ_[l]) hS (ZMod m) (shiftMat ℚ_[l] m) hM (shiftLog ℚ_[l] l m) hf hfE (ZMod m)
    (fun j => (l : ℚ_[l]) • shiftLog ℚ_[l] l m j) hg0 hgE
  set e : ZMod m → MvPowerSeries (ZMod m) ℤ_[l] := fun i => liftZ (h i) (hhI i) with he_def
  have he : ∀ i, map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e i) = h i :=
    fun i => map_liftZ (h i) (hhI i)
  have he0 : ∀ i, constantCoeff (e i) = 0 :=
    fun i => constantCoeff_of_map _ (by rw [he i]; exact hh0 i)
  have hF0 : ∀ i, constantCoeff (F i) = 0 := fun i => constantCoeff_of_map _ (hF.1 i)

  set FK : ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun i => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (F i) with hFK
  set EK : Fin 2 × ZMod m → MvPowerSeries (Fin 2 × ZMod m) ℚ_[l] :=
    fun x => if x.1 = 0 then atXv (h x.2) else atYv (h x.2) with hEK
  have hFKs : HasSubst FK := hasSubst0 FK hF.1
  have hhs : HasSubst h := hasSubst0 h hh0
  have hEK0 : ∀ x, constantCoeff (EK x) = 0 := by
    intro x
    simp only [hEK]
    split_ifs
    · exact constantCoeff_atXv (hh0 _)
    · exact constantCoeff_atYv (hh0 _)
  have hEKs : HasSubst EK := hasSubst0 EK hEK0

  have hkey : (fun i => subst FK (h i)) = (fun i => subst EK (FK i)) := by
    refine Formalism.FG.subst_injective_vector.{0, 0, 0} ℚ_[l] (ZMod m) (Fin 2 × ZMod m)
      (shiftLog ℚ_[l] l m) _ _ hf
      (fun i => constantCoeff_subst_eq_zero hFKs hF.1 (hh0 i))
      (fun i => constantCoeff_subst_eq_zero hEKs hEK0 (hF.1 i)) (fun j => ?_)
    rw [← subst_comp_subst_apply hhs hFKs, hh j, subst_smul hFKs, hF.2.2 j,
      ← subst_comp_subst_apply hFKs hEKs, hF.2.2 j, subst_add hEKs,
      subst_atXv EK hEKs, subst_atYv EK hEKs]
    have hx : (fun i => EK (0, i)) = fun i => atXv (h i) := by
      funext i; simp [hEK]
    have hy : (fun i => EK (1, i)) = fun i => atYv (h i) := by
      funext i; simp [hEK]
    rw [hx, hy, ← atXv_subst h hh0, ← atYv_subst h hh0, hh j, smul_add]
    unfold atXv atYv
    rw [subst_smul hasSubst_vX, subst_smul hasSubst_vY]
  have hFs : HasSubst F := hasSubst0 F hF0
  have hE0 : ∀ x : Fin 2 × ZMod m, constantCoeff
      ((fun x : Fin 2 × ZMod m => if x.1 = 0 then atXv (e x.2) else atYv (e x.2)) x) = 0 := by
    intro x
    simp only
    split_ifs
    · exact constantCoeff_atXv (he0 _)
    · exact constantCoeff_atYv (he0 _)
  have hHom : IsHomV F F e := by
    refine ⟨he0, fun i => ?_⟩
    apply coe_map_injective
    rw [map_subst hFs, map_subst (hasSubst0 _ hE0), he i]
    have := congrFun hkey i
    rw [this]
    congr 1
    funext x
    simp only [hEK]
    split_ifs
    · rw [map_atXv, he]
    · rw [map_atYv, he]
  have hfe : (fun k => map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e k)) = h := funext he

  set β : ZMod m → MvPowerSeries (ZMod m) ℚ_[l] := fun k => X (k - 1) ^ (l ^ 2) with hβ
  have hβ0 : ∀ k, constantCoeff (β k) = 0 := by
    intro k; simp [hβ, hlp.ne_zero]
  have hβI : ∀ k, IntegralMv (β k) := by
    intro k d; simp only [hβ]; rw [coeff_X_pow]; split_ifs <;> simp
  have hρs : HasSubst (fun k : ZMod m => (X (k - 1) : MvPowerSeries (ZMod m) ℚ_[l])) :=
    hasSubst0 _ (fun _ => constantCoeff_X _)
  have hβf : ∀ j, subst β (shiftLog ℚ_[l] l m j) =
      MvPowerSeries.expand (l ^ 2) hq (shiftLog ℚ_[l] l m (j - 1)) := by
    intro j
    have : β = fun k => MvPowerSeries.expand (l ^ 2) hq (X (k - 1)) := by
      funext k; simp [hβ]
    rw [this, ← expand_subst _ _ hρs, subst_shift_shiftLog hl2]
  have hdiv := (hC ℚ_[l] l (l ^ 2) hq (RingHom.id _) hS (ZMod m) (shiftMat ℚ_[l] m) hM
    (shiftLog ℚ_[l] l m) hf hfE (ZMod m) h β hh0 hβ0 hhI hβI 1 le_rfl).mpr (by
      intro j d
      rw [hh j, hβf j, hexp j, ← smul_sub, sub_sub_cancel, pow_one, coeff_smul, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hXI j d))
  have hcongr : ∀ j n, (l : ℤ_[l]) ∣ coeff n (e j - X (j - 1) ^ (l ^ 2)) := by
    intro j n
    apply dvd_of_norm_le
    have hmap : h j - β j =
        map (PadicInt.Coe.ringHom : ℤ_[l] →+* ℚ_[l]) (e j - X (j - 1) ^ (l ^ 2)) := by
      rw [map_sub, map_pow, map_X, he j]
    have := hdiv j n
    rw [hmap, coeff_map, pow_one] at this
    exact this

  have hred : ∀ j, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j) = X (j - 1) ^ (l ^ 2) := by
    intro j
    have h0 : map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (e j - X (j - 1) ^ (l ^ 2)) = 0 := by
      ext n
      rw [coeff_map, map_zero, toZMod_eq_zero_iff]
      exact hcongr j n
    rwa [map_sub, map_pow, map_X, sub_eq_zero] at h0
  have hit : ∀ n : ℕ, (∀ i, constantCoeff (iterV e n i) = 0) ∧
      ∀ i, map (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (iterV e n i) =
        X (i - (n : ZMod m)) ^ ((l ^ 2) ^ n) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp [iterV]
      · simp [iterV, map_X]
    | succ n ih =>
      have hsucc : ∀ i, iterV e (n + 1) i = subst (iterV e n) (e i) := by
        intro i
        simp only [iterV]
        rw [Function.iterate_succ_apply']
      have hs1 : HasSubst (iterV e n) := hasSubst0 _ ih.1
      refine ⟨fun i => ?_, fun i => ?_⟩
      · rw [hsucc]
        exact constantCoeff_subst_eq_zero hs1 ih.1 (he0 i)
      · rw [hsucc, map_subst hs1, hred i, subst_pow (hs1.map _), subst_X (hs1.map _), ih.2,
          ← pow_mul, ← pow_succ]
        congr 2
        push_cast
        ring
  refine ⟨e, hHom, fun j => by rw [hfe]; exact hh j, hcongr, fun j n => ?_⟩
  rw [← toZMod_eq_zero_iff, ← coeff_map, map_sub, (hit m).2 j, ZMod.natCast_self, sub_zero,
    ← pow_mul, map_pow, map_X, sub_self, map_zero]

end Main

end Formalism.FG.HeightVAux

namespace Formalism.FG

end Formalism.FG
