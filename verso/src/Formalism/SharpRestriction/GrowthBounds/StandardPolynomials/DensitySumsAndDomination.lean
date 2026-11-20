import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCore
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RecursionWithDensities
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.LatticeLeSpanPsiImage
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

section PolLem

variable {K : Type} [CommRing K] {ι : Type} {n : ℕ}

/- English proof (translation)
Rewrite using `[Pol, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_coe, ← MvPolynomial.C_1, MvPolynomial.C_apply]`. Establish `hm0` using `MvPolynomial.support_monomial_subset hm`. Rewrite `hm0` using `[Finset.mem_singleton]`.

Substitute `hm0` using the available equality. Introduce `i`. Simplify using `[multideg]`.
-/
theorem pol_one' : (1 : MvPolynomial (ι × Fin n) K) ∈ Pol K n (0 : ι → ℕ) := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  rw [Finset.mem_coe, ← MvPolynomial.C_1, MvPolynomial.C_apply] at hm
  have hm0 := MvPolynomial.support_monomial_subset hm
  rw [Finset.mem_singleton] at hm0
  subst hm0
  intro i
  simp [multideg]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using pol_one' (K := K) (ι := ι) (n := n)`. Consider the case `succ k ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `hom_Pol_mul K ih h`.
-/
theorem pol_pow' {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) K} (h : P ∈ Pol K n d) (k : ℕ) : P ^ k ∈ Pol K n (k • d) := by
  induction k with
  | zero => simpa using pol_one' (K := K) (ι := ι) (n := n)
  | succ k ih =>
    rw [pow_succ, succ_nsmul]
    exact hom_Pol_mul K ih h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using pol_one' (K := K) (ι := ι) (n := n)`. Consider the case `@insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `hom_Pol_mul K (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem pol_prod' {κ : Type} (s : Finset κ) (d : κ → ι → ℕ) (f : κ → MvPolynomial (ι × Fin n) K)
    (h : ∀ i ∈ s, f i ∈ Pol K n (d i)) : ∏ i ∈ s, f i ∈ Pol K n (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pol_one' (K := K) (ι := ι) (n := n)
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact hom_Pol_mul K (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Unfold `multideg`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[Finsupp.single_apply]`. Simplify using `[Finsupp.single_apply, Ne.symm h, h]`.
-/
theorem multideg_single' [DecidableEq ι] (a : ι) (c : Fin n) (k : ℕ) (i : ι) :
    multideg (Finsupp.single (a, c) k) i = if i = a then k else 0 := by
  unfold multideg
  by_cases h : i = a
  · subst h
    simp [Finsupp.single_apply]
  · simp [Finsupp.single_apply, Ne.symm h, h]

/- English proof (translation)
Rewrite using `[Pol, MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_X]`. Introduce `m hm`. Rewrite `hm` using `[Finset.coe_singleton, Set.mem_singleton_iff]`. Substitute `hm` using the available equality. Introduce `i`.

Conclude with `multideg_single' a c 1 i`.
-/
theorem pol_X' [DecidableEq ι] [Nontrivial K] (a : ι) (c : Fin n) :
    (X (a, c) : MvPolynomial (ι × Fin n) K) ∈ Pol K n (fun i => if i = a then 1 else 0) := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff, MvPolynomial.support_X]
  intro m hm
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hm
  subst hm
  intro i
  exact multideg_single' a c 1 i

end PolLem

section Coarse

variable {O : Type} [CommRing O] [IsDomain O] {s r : ℕ} [NeZero r]

def pairU (K : Type) [CommRing K] (r : ℕ) (S : SegData s) (l : Fin S.t) : MvPolynomial (Fin (2 * s + 1) × Fin r) K :=
  tcPairP K (chW (uTop S l)) (chE (uTop S l))

/- English proof (translation)
Establish `hd : (fun a : Fin (2 * s + 1) => if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then 1 else 0) = (fun a => if a = chW (uTop S l) then 1 else 0) + (fun a => if a = chE (uTop S l) then 1 else 0)`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply, Fin.ext_iff, chW, chE, uTop, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[hd]`.

Unfold `pairU tcPairP`. Conclude with `Submodule.sum_mem _ fun c _ => hom_Pol_mul K (pol_X' _ c) (pol_X' _ c)`.
-/
theorem pairU_pol (K : Type) [CommRing K] [Nontrivial K] (S : SegData s) (l : Fin S.t) :
    pairU K r S l ∈ Pol K r (fun a : Fin (2 * s + 1) =>
      if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then 1 else 0) := by
  have hd : (fun a : Fin (2 * s + 1) =>
      if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then 1 else 0) =
      (fun a => if a = chW (uTop S l) then 1 else 0) + (fun a => if a = chE (uTop S l) then 1 else 0) := by
    funext a
    simp only [Pi.add_apply, Fin.ext_iff, chW, chE, uTop, Fin.val_mk]
    split_ifs <;> omega
  rw [hd]
  unfold pairU tcPairP
  exact Submodule.sum_mem _ fun c _ => hom_Pol_mul K (pol_X' _ c) (pol_X' _ c)

/- English proof (translation)
Establish `key : (fun a : Fin (2 * s + 1) => jE S k (a.val / 2)) = ∑ l, k l • (fun a : Fin (2 * s + 1) => if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then 1 else 0)`. Use function extensionality and compare the values at `a`. Rewrite using `[Finset.sum_apply, ← tieSum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`.

Rewrite using `[key]`. Conclude with `pol_prod' Finset.univ _ _ fun l _ => pol_pow' (pairU_pol K S l) (k l)`.
-/
theorem pairProd_pol (K : Type) [CommRing K] [Nontrivial K] (S : SegData s) (k : Fin S.t → ℕ) :
    ∏ l, pairU K r S l ^ k l ∈ Pol K r (fun a : Fin (2 * s + 1) => jE S k (a.val / 2)) := by
  have key : (fun a : Fin (2 * s + 1) => jE S k (a.val / 2)) =
      ∑ l, k l • (fun a : Fin (2 * s + 1) =>
        if a.val = 2 * (S.sigma + l.val) ∨ a.val = 2 * (S.sigma + l.val) + 1 then 1 else 0) := by
    funext a
    rw [Finset.sum_apply, ← tieSum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [key]
  exact pol_prod' Finset.univ _ _ fun l _ => pol_pow' (pairU_pol K S l) (k l)

/- English proof (translation)
Rewrite using `[IntPol, LinearMap.mem_range]`. Use `⟨pairU O r S l, ?_⟩` and prove the remaining obligations. Simplify using `[pairU, tcPairP, MvPolynomial.mapAlgHom_apply]`.
-/
theorem pairU_int (S : SegData s) (l : Fin S.t) : pairU (KK O) r S l ∈ IntPol O (Fin (2 * s + 1) × Fin r) := by
  rw [IntPol, LinearMap.mem_range]
  refine ⟨pairU O r S l, ?_⟩
  simp [pairU, tcPairP, MvPolynomial.mapAlgHom_apply]

/- English proof (translation)
Rewrite `hx`, the goal using `[IntPol, LinearMap.mem_range]`. Take `⟨a, rfl⟩` from `hx`. Conclude with `⟨a ^ k, by simp⟩`.
-/
theorem intPol_pow' {σ : Type} {x : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (k : ℕ) : x ^ k ∈ IntPol O σ := by
  rw [IntPol, LinearMap.mem_range] at hx ⊢
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a ^ k, by simp⟩

/- English proof (translation)
Conclude with `zsmul_mem hx z`.
-/
theorem zsmul_mem_sub {σ : Type} (M : Submodule O (MvPolynomial σ (KK O))) {x : MvPolynomial σ (KK O)} (hx : x ∈ M) (z : ℤ) :
    z • x ∈ M := by
  exact zsmul_mem hx z

/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[IntPol, LinearMap.mem_range]`. Take `⟨a, rfl⟩` from `hx`. Take `⟨b, rfl⟩` from `hy`. Conclude with `⟨a * b, by simp⟩`.
-/
theorem intPol_mul' {σ : Type} {x y : MvPolynomial σ (KK O)} (hx : x ∈ IntPol O σ) (hy : y ∈ IntPol O σ) :
    x * y ∈ IntPol O σ := by
  rw [IntPol, LinearMap.mem_range] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, by simp⟩

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, IntPol, LinearMap.mem_range]`. Conclude with `⟨1, by simp⟩`. Consider the case `@insert a t ha ih`.

Rewrite using `[Finset.prod_insert ha]`. Conclude with `intPol_mul' (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem intPol_prod' {σ κ : Type} (t : Finset κ) (f : κ → MvPolynomial σ (KK O)) (h : ∀ i ∈ t, f i ∈ IntPol O σ) :
    ∏ i ∈ t, f i ∈ IntPol O σ := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, IntPol, LinearMap.mem_range]
    exact ⟨1, by simp⟩
  | @insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact intPol_mul' (h a (Finset.mem_insert_self a t)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `set m : BVar N r t →₀ ℕ := ∑ c, Finsupp.single (xiVar N r t c) (γ c) with hm`. Establish `hmono : (∏ c, X (xiVar N r t c) ^ γ c : MvPolynomial (BVar N r t) (KK O)) = monomial m 1`. Rewrite using `[hm, MvPolynomial.monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun c _ => MvPolynomial.X_pow_eq_monomial`. Establish `hinj : Function.Injective (xiVar N r t)` using `fun c c' h => by`.

Simplify `h` using `[xiVar]`. Establish `hval : ∀ c', m (xiVar N r t c') = γ c'`. Introduce `c'`. Rewrite using `[hm, Finsupp.finset_sum_apply]`. Simplify using `[Finsupp.single_apply, hinj.eq_iff]`.

Rewrite using `[hmono]`. Use `Submodule.mem_inf.mpr ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]`. Introduce `m' hm'`. Establish `hm''` using `MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm')`.

Rewrite `hm''` using `[Finset.mem_singleton]`. Substitute `hm''` using the available equality. Use `⟨fun v hv => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hv` using `[hm]`. Take `⟨c, -, hc⟩` from `Finset.mem_biUnion.mp (Finsupp.support_finset_sum hv)`.

Conclude with `⟨c, Finset.mem_singleton.mp (Finsupp.support_single_subset hc)⟩`. Simplify using `only [hval]`. Conclude with `hb`. Rewrite using `[IntPol, LinearMap.mem_range]`. Conclude with `⟨monomial m 1, by simp⟩`.
-/
theorem xi_mono_mem (N t b : ℕ) (γ : Fin r → ℕ) (hb : ∑ c, γ c = b) :
    (∏ c, X (xiVar N r t c) ^ γ c : MvPolynomial (BVar N r t) (KK O)) ∈ XiPolZ O N r t b := by
  set m : BVar N r t →₀ ℕ := ∑ c, Finsupp.single (xiVar N r t c) (γ c) with hm
  have hmono : (∏ c, X (xiVar N r t c) ^ γ c : MvPolynomial (BVar N r t) (KK O)) = monomial m 1 := by
    rw [hm, MvPolynomial.monomial_sum_one]
    exact Finset.prod_congr rfl fun c _ => MvPolynomial.X_pow_eq_monomial
  have hinj : Function.Injective (xiVar N r t) := fun c c' h => by
    simpa [xiVar] using h
  have hval : ∀ c', m (xiVar N r t c') = γ c' := by
    intro c'
    rw [hm, Finsupp.finset_sum_apply]
    simp [Finsupp.single_apply, hinj.eq_iff]
  rw [hmono]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    have hm'' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hm')
    rw [Finset.mem_singleton] at hm''
    subst hm''
    refine ⟨fun v hv => ?_, ?_⟩
    · rw [hm] at hv
      obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (Finsupp.support_finset_sum hv)
      exact ⟨c, Finset.mem_singleton.mp (Finsupp.support_single_subset hc)⟩
    · simp only [hval]
      exact hb
  · rw [IntPol, LinearMap.mem_range]
    exact ⟨monomial m 1, by simp⟩

variable (O) (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (mu : ℝ) (b' : SegBlock s r)

def EhS (r : ℕ) (S : SegData s) (l : Fin S.t) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
  X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) * X (scalS (2 * s + 1) r S.t (Fin.castSucc l)) +
    ∑ c, X (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ)), c)) *
      X (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1), c))

def EpS (r : ℕ) (S : SegData s) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
  X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) * X (scalS (2 * s + 1) r S.t (Fin.last S.t)) +
    ∑ c, X (Sum.inl (Fin.castSucc (⟨2 * s, by omega⟩ : Fin (2 * s + 1)), c)) * X (xiVar (2 * s + 1) r S.t c)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ehat_rfl (l : Fin S.t) : (blockData p S aTop aPlus mu b').Ehat O (r := r) l = EhS O r S l := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Eplus_rfl : (blockData p S aTop aPlus mu b').Eplus O (r := r) = EpS O r S := rfl

/- English proof (translation)
Establish `hl` using `l.2`. Unfold `SegData.t at hl`. Establish `h1 : finPos (2 * s + 1) (2 * (uTop S l : ℕ)) = Fin.castSucc (chW (uTop S l))`. Use `ext`. Simplify using `only [finPos, chW, uTop, Fin.val_castSucc, Fin.val_mk]`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1) = Fin.castSucc (chE (uTop S l))`. Use `ext`. Simplify using `only [finPos, chE, uTop, Fin.val_castSucc, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [EhS, pairU, tcPairP, map_sum, map_mul, rename_X, chainEmb, h1, h2]`.
-/
theorem EhS_eq (l : Fin S.t) :
    EhS O r S l =
      X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) * X (scalS (2 * s + 1) r S.t (Fin.castSucc l)) +
        rename (chainEmb (2 * s + 1) r S.t) (pairU (KK O) r S l) := by
  have hl := l.2
  unfold SegData.t at hl
  have h1 : finPos (2 * s + 1) (2 * (uTop S l : ℕ)) = Fin.castSucc (chW (uTop S l)) := by
    ext
    simp only [finPos, chW, uTop, Fin.val_castSucc, Fin.val_mk]
    omega
  have h2 : finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1) = Fin.castSucc (chE (uTop S l)) := by
    ext
    simp only [finPos, chE, uTop, Fin.val_castSucc, Fin.val_mk]
    omega
  simp only [EhS, pairU, tcPairP, map_sum, map_mul, rename_X, chainEmb, h1, h2]

def uTot (r : ℕ) (S : SegData s) (ju : Fin S.t → ℕ) (jp : ℕ) (G : MvPolynomial (Fin (2 * s + 1) × Fin r) (KK O))
    (zU sU : Fin S.t → ℕ) (xf : ℕ) (γ : Fin r → ℕ) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
  (∏ l : Fin S.t, EhS O r S l ^ ju l) * EpS O r S ^ jp * rename (chainEmb (2 * s + 1) r S.t) G *
    (∏ l : Fin S.t, (X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) ^ zU l * X (scalS (2 * s + 1) r S.t (Fin.castSucc l)) ^ sU l)) *
    X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c

variable {O p S aTop aPlus mu b'}

/- English proof (translation)
Substitute `hx` using the available equality. Establish `hi` using `i.2`. Unfold `SegData.t at hi`. Unfold `jE`. Rewrite using `[dif_pos (show S.sigma ≤ S.sigma + i.val ∧ S.sigma + i.val < s from ⟨by omega, by omega⟩)]`.

Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
private theorem jE_apply_sigma_add (S : SegData s) (f : Fin S.t → ℕ) (i : Fin S.t) (x : ℕ) (hx : x = S.sigma + i.val) :
    jE S f x = f i := by
  subst hx
  have hi := i.2
  unfold SegData.t at hi
  unfold jE
  rw [dif_pos (show S.sigma ≤ S.sigma + i.val ∧ S.sigma + i.val < s from ⟨by omega, by omega⟩)]
  congr 1
  ext
  simp

/- English proof (translation)
Unfold `jE`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem jE_add' (S : SegData s) (f g : Fin S.t → ℕ) (x : ℕ) :
    jE S (fun l => f l + g l) x = jE S f x + jE S g x := by
  unfold jE
  split_ifs <;> simp

/- English proof (translation)
Unfold `jE`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem jE_sub_eq_sub_jE (S : SegData s) (f g : Fin S.t → ℕ) (x : ℕ) :
    jE S (fun l => f l - g l) x = jE S f x - jE S g x := by
  unfold jE
  split_ifs <;> simp

/- English proof (translation)
Unfold `jE`. Use `split_ifs`. Conclude with `h _`. Conclude with `le_refl 0`.
-/
private theorem jE_mono' (S : SegData s) (f g : Fin S.t → ℕ) (h : ∀ l, g l ≤ f l) (x : ℕ) :
    jE S g x ≤ jE S f x := by
  unfold jE
  split_ifs
  · exact h _
  · exact le_refl 0

/- English proof (translation)
Use `set E : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) := fun l => EhS O r S l with hE`. Use `set R : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) := fun l => rename (chainEmb (2 * s + 1) r S.t) (pairU (KK O) r S l) with hR`. Use `set Zv : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) := fun l => X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) with hZv`. Use `set Sv : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) := fun l => X (scalS (2 * s + 1) r S.t (Fin.castSucc l)) with hSv`. Establish `hZS : ∀ l, Zv l ^ zU l * Sv l ^ sU l = Zv l ^ (zU l - sU l) * ∑ m ∈ Finset.range (sU l + 1), E l ^ m * (-R l) ^ (sU l - m) * ((sU l).choose m : MvPolynomial _ (KK O))`.

Introduce `l`. Rewrite using `[← add_pow]`. Establish `e1 : E l + -R l = Zv l * Sv l`. Simplify using `only [hE, hR, hZv, hSv]`. Rewrite using `[EhS_eq]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hs l)]`. Establish `hexp : ∏ l, (Zv l ^ zU l * Sv l ^ sU l) = (∏ l, Zv l ^ (zU l - sU l)) * ∑ m ∈ Fintype.piFinset (fun l => Finset.range (sU l + 1)), ∏ l, (E l ^ m l * (-R l) ^ (sU l - m l) * ((sU l).choose (m l) : MvPolynomial _ (KK O)))`. Rewrite using `[Finset.prod_congr rfl fun l _ => hZS l, Finset.prod_mul_distrib, Finset.prod_univ_sum]`. Unfold `uTot`.

Rewrite using `[hexp]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hm' : ∀ l, m l ≤ sU l` using `fun l => Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hm l))`. Use `set cf : ℤ := ∏ l, ((-1) ^ (sU l - m l) * ((sU l).choose (m l) : ℤ)) with hcf`.

Use `set y := G * ∏ l, pairU (KK O) r S l ^ (sU l - m l) with hy`. Establish `eterm : (∏ l, E l ^ ju l) * EpS O r S ^ jp * rename (chainEmb (2 * s + 1) r S.t) G * ((∏ l, Zv l ^ (zU l - sU l)) * ∏ l, (E l ^ m l * (-R l) ^ (sU l - m l) * ((sU l).choose (m l) : MvPolynomial _ (KK O)))) * X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf * ∏ c, X (xiVar (2 * s + …`. Rewrite using `[zsmul_eq_mul, hcf, hy]`. Simplify using `only [pow_add, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, Int.cast_prod, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]`. Establish `e2 : ∏ l, (-R l) ^ (sU l - m l) = (∏ l, (-1 : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) ^ (sU l - m l)) * ∏ l, R l ^ (sU l - m l)`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun l _ => neg_pow _ _`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eterm]`.

Use `zsmul_mem_sub _ (Submodule.subset_span ?_) cf` and prove the remaining obligations. Use `Set.mem_iUnion.2 ⟨fun l => ju l + m l, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩` and prove the remaining obligations. Establish `hLv : ∀ l : Fin S.t, ju l + m l ≤ (segChain p S aTop b').deg ((blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ))) ∧ ju l + m l ≤ (segChain p S aTop b').deg ((blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ) + 1))`. Introduce `l`. Establish `hl : l.val < s - S.sigma` using `l.2`.

Establish `a1 : (blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ)) = chW (uTop S l)`. Apply `Fin.ext` to reduce the goal to its premises. Use `show min (2 * (S.sigma + l.val)) (2 * s + 1 - 1) = 2 * (S.sigma + l.val)`. Use linear arithmetic over natural numbers and integers. Establish `a2 : (blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ) + 1) = chE (uTop S l)`.

Apply `Fin.ext` to reduce the goal to its premises. Use `show min (2 * (S.sigma + l.val) + 1) (2 * s + 1 - 1) = 2 * (S.sigma + l.val) + 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[a1, a2]`. Establish `d1` using `hdeg (chW (uTop S l))`.

Establish `d2` using `hdeg (chE (uTop S l))`. Establish `q1 : (chW (uTop S l)).val / 2 = S.sigma + l.val` using `by show 2 * (S.sigma + l.val) / 2 = _`. Use linear arithmetic over natural numbers and integers. Establish `q2 : (chE (uTop S l)).val / 2 = S.sigma + l.val` using `by show (2 * (S.sigma + l.val) + 1) / 2 = _`. Use linear arithmetic over natural numbers and integers.

Rewrite `d1` using `[q1, jE_at]`. Rewrite `d2` using `[q2, jE_at]`. Use `hm' l` as an intermediate fact. Apply the tactic sequence `constructor <;> omega`. Use `⟨fun l => hLv l, ?_⟩` and prove the remaining obligations.

Establish `d1` using `hdeg (chU s)`. Rewrite `d1` using `[if_pos (show (chU s).val = 2 * s from rfl)]`. Use `show jp ≤ min ((segChain p S aTop b').deg (chU s)) S.bPlus`. Conclude with `le_min (by omega) (by omega)`. Use `⟨y, ⟨⟨?_, ?_⟩, ?_⟩, ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1` using `hom_Pol_mul (KK O) hGP (pairProd_pol (r := r) (KK O) S (fun l => sU l - m l))`. Establish `hd : ((blockData p S aTop aPlus mu b').lettersAt (fun l => ju l + m l) jp).deg = dG + fun a : Fin (2 * s + 1) => jE S (fun l => sU l - m l) (a.val / 2)`. Use function extensionality and compare the values at `a`. Use `(lev_deg p S aTop aPlus mu b' (fun l => ju l + m l) jp a).trans ?_` and prove the remaining obligations. Rewrite using `[hdeg a]`.

Simplify using `only [Pi.add_apply]`. Establish `hj : jE S (fun l => ju l + sU l) (a.val / 2) = jE S (fun l => ju l + m l) (a.val / 2) + jE S (fun l => sU l - m l) (a.val / 2)`. Unfold `jE`. Use `split_ifs with h`. Use `hm' ⟨a.val / 2 - S.sigma, by unfold SegData.t; omega⟩ dsimp only` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression. Use linear arithmetic over natural numbers and integers. Use `show y ∈ Pol (KK O) r ((blockData p S aTop aPlus mu b').lettersAt (fun l => ju l + m l) jp).deg`. Rewrite using `[hd]`.

Conclude with `h1`. Conclude with `(Submodule.mem_iInf _).2 fun k => hY m hm' k`. Conclude with `intPol_mul' hGI (intPol_prod' _ _ fun l _ => intPol_pow' (pairU_int S l) _)`. Use `show _ ∈ XiPolZ O (2 * s + 1) r S.t (S.bPlus - jp)`. Conclude with `xi_mono_mem _ _ _ γ (by omega)`.

Establish `hfin : (∏ l, E l ^ (ju l + m l)) * EpS O r S ^ jp * (∏ l, Zv l ^ (zU l - sU l)) * X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf * rename (chainEmb (2 * s + 1) r S.t) y * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c = (∏ l, E l ^ (ju l + m l)) * EpS O r S ^ jp * (∏ l : Fin S.t, Zv l …`. Simplify using `only [hz, hx]`. Conclude with `hfin`.
-/
theorem uTot_mem {ju : Fin S.t → ℕ} {jp : ℕ} {G : MvPolynomial (Fin (2 * s + 1) × Fin r) (KK O)} {zU sU : Fin S.t → ℕ}
    {xf : ℕ} {γ : Fin r → ℕ} (hs : ∀ l, sU l ≤ zU l)
    (hz : ∀ l, coarseA p S b' (uTop S l) - b'.o (uTop S l) = zU l - sU l) (hx : aPlus - b'.oPlus = xf)
    (dG : Fin (2 * s + 1) → ℕ) (hGI : G ∈ IntPol O (Fin (2 * s + 1) × Fin r)) (hGP : G ∈ Pol (KK O) r dG)
    (hdeg : ∀ a : Fin (2 * s + 1), (segChain p S aTop b').deg a =
      dG a + jE S (fun l => ju l + sU l) (a.val / 2) + if a.val = 2 * s then jp else 0)
    (hB : S.bPlus = jp + ∑ c, γ c)
    (hY : ∀ m : Fin S.t → ℕ, (∀ l, m l ≤ sU l) → ∀ k,
      G * ∏ l, pairU (KK O) r S l ^ (sU l - m l) ∈
        YCond (KK O) (r := r) ((blockData p S aTop aPlus mu b').lettersAt (fun l => ju l + m l) jp)
          ((blockData p S aTop aPlus mu b').T.J k) ((blockData p S aTop aPlus mu b').T.thr k)) :
    uTot O r S ju jp G zU sU xf γ ∈ (blockData p S aTop aPlus mu b').SSZ O (r := r) := by
  classical
  set E : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
    fun l => EhS O r S l with hE
  set R : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
    fun l => rename (chainEmb (2 * s + 1) r S.t) (pairU (KK O) r S l) with hR
  set Zv : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
    fun l => X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) with hZv
  set Sv : Fin S.t → MvPolynomial (BVar (2 * s + 1) r S.t) (KK O) :=
    fun l => X (scalS (2 * s + 1) r S.t (Fin.castSucc l)) with hSv
  have hZS : ∀ l, Zv l ^ zU l * Sv l ^ sU l = Zv l ^ (zU l - sU l) *
      ∑ m ∈ Finset.range (sU l + 1), E l ^ m * (-R l) ^ (sU l - m) * ((sU l).choose m : MvPolynomial _ (KK O)) := by
    intro l
    rw [← add_pow]
    have e1 : E l + -R l = Zv l * Sv l := by
      simp only [hE, hR, hZv, hSv]
      rw [EhS_eq]
      ring
    rw [e1, mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (hs l)]
  have hexp : ∏ l, (Zv l ^ zU l * Sv l ^ sU l) = (∏ l, Zv l ^ (zU l - sU l)) *
      ∑ m ∈ Fintype.piFinset (fun l => Finset.range (sU l + 1)),
        ∏ l, (E l ^ m l * (-R l) ^ (sU l - m l) * ((sU l).choose (m l) : MvPolynomial _ (KK O))) := by
    rw [Finset.prod_congr rfl fun l _ => hZS l, Finset.prod_mul_distrib, Finset.prod_univ_sum]
  unfold uTot
  rw [hexp]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' : ∀ l, m l ≤ sU l := fun l =>
    Nat.lt_succ_iff.1 (Finset.mem_range.1 (Fintype.mem_piFinset.1 hm l))
  set cf : ℤ := ∏ l, ((-1) ^ (sU l - m l) * ((sU l).choose (m l) : ℤ)) with hcf
  set y := G * ∏ l, pairU (KK O) r S l ^ (sU l - m l) with hy
  have eterm : (∏ l, E l ^ ju l) * EpS O r S ^ jp *
        rename (chainEmb (2 * s + 1) r S.t) G * ((∏ l, Zv l ^ (zU l - sU l)) *
          ∏ l, (E l ^ m l * (-R l) ^ (sU l - m l) * ((sU l).choose (m l) : MvPolynomial _ (KK O)))) *
        X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c =
      cf • ((∏ l, E l ^ (ju l + m l)) * EpS O r S ^ jp *
        (∏ l, Zv l ^ (zU l - sU l)) * X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf *
        rename (chainEmb (2 * s + 1) r S.t) y * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c) := by
    rw [zsmul_eq_mul, hcf, hy]
    simp only [pow_add, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, Int.cast_prod, Int.cast_mul, Int.cast_pow,
      Int.cast_neg, Int.cast_one, Int.cast_natCast]
    have e2 : ∏ l, (-R l) ^ (sU l - m l) = (∏ l, (-1 : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) ^ (sU l - m l)) *
        ∏ l, R l ^ (sU l - m l) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun l _ => neg_pow _ _
    rw [e2]
    ring
  rw [eterm]
  refine zsmul_mem_sub _ (Submodule.subset_span ?_) cf
  refine Set.mem_iUnion.2 ⟨fun l => ju l + m l, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩⟩
  ·
    have hLv : ∀ l : Fin S.t,
        ju l + m l ≤ (segChain p S aTop b').deg ((blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ))) ∧
        ju l + m l ≤ (segChain p S aTop b').deg ((blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ) + 1)) := by
      intro l
      have hl : l.val < s - S.sigma := l.2
      have a1 : (blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ)) = chW (uTop S l) := by
        apply Fin.ext
        show min (2 * (S.sigma + l.val)) (2 * s + 1 - 1) = 2 * (S.sigma + l.val)
        omega
      have a2 : (blockData p S aTop aPlus mu b').letterAt (2 * (uTop S l : ℕ) + 1) = chE (uTop S l) := by
        apply Fin.ext
        show min (2 * (S.sigma + l.val) + 1) (2 * s + 1 - 1) = 2 * (S.sigma + l.val) + 1
        omega
      rw [a1, a2]
      have d1 := hdeg (chW (uTop S l))
      have d2 := hdeg (chE (uTop S l))
      have q1 : (chW (uTop S l)).val / 2 = S.sigma + l.val := by
        show 2 * (S.sigma + l.val) / 2 = _
        omega
      have q2 : (chE (uTop S l)).val / 2 = S.sigma + l.val := by
        show (2 * (S.sigma + l.val) + 1) / 2 = _
        omega
      rw [q1, jE_at] at d1
      rw [q2, jE_at] at d2
      have := hm' l
      constructor <;> omega
    refine ⟨fun l => hLv l, ?_⟩
    have d1 := hdeg (chU s)
    rw [if_pos (show (chU s).val = 2 * s from rfl)] at d1
    show jp ≤ min ((segChain p S aTop b').deg (chU s)) S.bPlus
    exact le_min (by omega) (by omega)
  · refine ⟨y, ⟨⟨?_, ?_⟩, ?_⟩, ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c, ?_, ?_⟩
    ·
      have h1 := hom_Pol_mul (KK O) hGP (pairProd_pol (r := r) (KK O) S (fun l => sU l - m l))
      have hd : ((blockData p S aTop aPlus mu b').lettersAt (fun l => ju l + m l) jp).deg =
          dG + fun a : Fin (2 * s + 1) => jE S (fun l => sU l - m l) (a.val / 2) := by
        funext a
        refine (lev_deg p S aTop aPlus mu b' (fun l => ju l + m l) jp a).trans ?_
        rw [hdeg a]
        simp only [Pi.add_apply]
        have hj : jE S (fun l => ju l + sU l) (a.val / 2) =
            jE S (fun l => ju l + m l) (a.val / 2) + jE S (fun l => sU l - m l) (a.val / 2) := by
          unfold jE
          split_ifs with h
          · have := hm' ⟨a.val / 2 - S.sigma, by unfold SegData.t; omega⟩
            dsimp only
            omega
          · rfl
        omega
      show y ∈ Pol (KK O) r ((blockData p S aTop aPlus mu b').lettersAt (fun l => ju l + m l) jp).deg
      rw [hd]
      exact h1
    · exact (Submodule.mem_iInf _).2 fun k => hY m hm' k
    · exact intPol_mul' hGI (intPol_prod' _ _ fun l _ => intPol_pow' (pairU_int S l) _)
    · show _ ∈ XiPolZ O (2 * s + 1) r S.t (S.bPlus - jp)
      exact xi_mono_mem _ _ _ γ (by omega)
    · have hfin : (∏ l, E l ^ (ju l + m l)) * EpS O r S ^ jp *
          (∏ l, Zv l ^ (zU l - sU l)) * X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ xf *
          rename (chainEmb (2 * s + 1) r S.t) y * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c =
        (∏ l, E l ^ (ju l + m l)) * EpS O r S ^ jp *
          (∏ l : Fin S.t, Zv l ^ (coarseA p S b' (uTop S l) - b'.o (uTop S l))) *
          X (scalZ (2 * s + 1) r S.t (Fin.last S.t)) ^ (aPlus - b'.oPlus) *
          rename (chainEmb (2 * s + 1) r S.t) y * ∏ c, X (xiVar (2 * s + 1) r S.t c) ^ γ c := by
        simp only [hz, hx]
      exact hfin

end Coarse

end Formalism.MainNotions.ColumnSystems.Pf
