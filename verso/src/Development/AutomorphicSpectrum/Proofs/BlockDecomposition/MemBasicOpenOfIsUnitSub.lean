import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.RootPowLC

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty`. Rewrite using `[Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]`. Discharge the goal by the elementary cases of `trivial`. Consider the case `insert a t ha ih`.

Rewrite using `[Finset.prod_insert ha, Scheme.basicOpen_mul]`. Conclude with `⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩`.
-/
theorem mem_basicOpen_prod {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤)) (u : U)
    (h : ∀ a ∈ t, u ∈ U.basicOpen (s a)) : u ∈ U.basicOpen (∏ a ∈ t, s a) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, U.basicOpen_of_isUnit isUnit_one]
    trivial
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul]
    exact ⟨h a (Finset.mem_insert_self a t), ih fun b hb => h b (Finset.mem_insert_of_mem hb)⟩

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hm` using `mem_basicOpen_prod t s u hc`. Rewrite `hm` using `[h, Scheme.basicOpen_zero]`. Conclude with `hm`.
-/
theorem exists_notMem_basicOpen {U : Scheme.{0}} {ι : Type} (t : Finset ι) (s : ι → Γ(U, ⊤))
    (h : ∏ a ∈ t, s a = 0) (u : U) : ∃ a ∈ t, u ∉ U.basicOpen (s a) := by
  by_contra hc
  push_neg at hc
  have hm := mem_basicOpen_prod t s u hc
  rw [h, Scheme.basicOpen_zero] at hm
  exact hm

/- English proof (translation)
Rewrite `hx`, the goal using `[Scheme.mem_basicOpen_top]`. Establish `h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y))` using `h.map _`. Rewrite `h1` using `[map_sub, sub_eq_add_neg]`. Break down `IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2` into its components or cases. Conclude with `absurd h2 hx`.

Simplify using `using h2.neg`.
-/
theorem mem_basicOpen_of_isUnit_sub {U : Scheme.{0}} (x y : Γ(U, ⊤)) (h : IsUnit (x - y)) (u : U)
    (hx : u ∉ U.basicOpen x) : u ∈ U.basicOpen y := by
  rw [Scheme.mem_basicOpen_top] at hx ⊢
  have h1 : IsUnit (U.presheaf.germ ⊤ u trivial (x - y)) := h.map _
  rw [map_sub, sub_eq_add_neg] at h1
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h1 with h2 | h2
  · exact absurd h2 hx
  · simpa using h2.neg

/- English proof (translation)
Use `RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_` and prove the remaining obligations. Establish `e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x` using `(Scheme.preimage_basicOpen g x).symm`. Establish `hv : v ∈ V.basicOpen (g.appTop.hom x)`. Rewrite using `[e]`. Conclude with `h v`.

Conclude with `(Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv`.
-/
theorem isUnit_appTop_of_mem {V U : Scheme.{0}} (g : V ⟶ U) (x : Γ(U, ⊤))
    (h : ∀ v : V, g v ∈ U.basicOpen x) : IsUnit (g.appTop.hom x) := by
  refine RingedSpace.isUnit_of_isUnit_germ V.toRingedSpace ⊤ _ fun v _ => ?_
  have e : V.basicOpen (g.appTop.hom x) = g ⁻¹ᵁ U.basicOpen x := (Scheme.preimage_basicOpen g x).symm
  have hv : v ∈ V.basicOpen (g.appTop.hom x) := by
    rw [e]
    exact h v
  exact (Scheme.mem_basicOpen_top V (g.appTop.hom x) v).1 hv

/- English proof (translation)
Establish `hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0`. Rewrite using `[← (hP q _ ζ).2.2.1 r, hr, sub_self]`. Establish `hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val)`. Introduce `u`. Take `⟨a, -, ha⟩` from `exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u`.

Conclude with `⟨a, ha⟩`. Establish `huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) → u ∈ U.basicOpen (r - ζ.1 ^ b.val)`. Introduce `u a b hab ha`. Apply `mem_basicOpen_of_isUnit_sub _ _ _ u ha` to reduce the goal to its premises. Establish `hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val` using `by ring`.

Rewrite using `[hd]`. Conclude with `(hP q _ ζ).2.1 b a (Ne.symm hab)`. Take `⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u)` from `⟨_, rfl⟩`. Establish `hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val)`. Introduce `u`.

Rewrite using `[hf0def]`. Conclude with `Classical.choose_spec (hex u)`. Establish `hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val)`. Introduce `u a`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `rfl`. Conclude with `hf0 u`. Introduce `ha`. Assume the negation of the conclusion as `hne`. Conclude with `(hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)`.

Establish `hloc : IsLocallyConstant f0`. Rewrite using `[IsLocallyConstant.iff_isOpen_fiber]`. Introduce `a`. Establish `hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U)`. Use extensionality with `u`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ, and_true, SetLike.mem_coe]`. Rewrite using `[hf0_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `ha b hb`. Conclude with `huniq u a b (Ne.symm hb) ha`.

Introduce `h ha`. Take `⟨a', ha'⟩` from `hex u`. Distinguish the cases in `heq : a' = a`. Conclude with `ha' (heq ▸ ha)`. Conclude with `ha' (h a' heq)`.

Rewrite using `[hfib]`. Conclude with `isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen`. Use `⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩` and prove the remaining obligations. Use `delta CrystallineSemistableComparison.E.IsPow`. Introduce `V g a hga`.

Establish `hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val))` using `fun b hb => isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))`. Establish `hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0`. Establish `h0` using `congrArg g.appTop.hom hprod`. Rewrite `h0` using `[map_prod, map_zero]`. Simplify `h0` using `only [map_sub, map_pow]`.

Rewrite `hprodV` using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]`. Establish `hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val))`. Use `Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)` and prove the remaining obligations. Establish `h1` using `hunitb b (Finset.ne_of_mem_erase hb)`. Simplify `h1` using `only [map_sub, map_pow]`.

Establish `h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0` using `hu.mul_left_eq_zero.mp hprodV`. Use `show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem exists_isPow (hP : PrimAlg) (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤))
    (r : Γ(U, ⊤)) (hr : r ^ q = 1) :
    ∃ f : LocallyConstant U (ZMod q), IsPow ζ f r ∧
      ∀ (u : U) (a : ZMod q), u ∉ U.basicOpen (r - ζ.1 ^ a.val) → f u = a := by
  classical
  have hprod : ∏ a : ZMod q, (r - ζ.1 ^ a.val) = 0 := by
    rw [← (hP q _ ζ).2.2.1 r, hr, sub_self]
  have hex : ∀ u : U, ∃ a : ZMod q, u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ (fun a : ZMod q => r - ζ.1 ^ a.val) hprod u
    exact ⟨a, ha⟩
  have huniq : ∀ (u : U) (a b : ZMod q), a ≠ b → u ∉ U.basicOpen (r - ζ.1 ^ a.val) →
      u ∈ U.basicOpen (r - ζ.1 ^ b.val) := by
    intro u a b hab ha
    apply mem_basicOpen_of_isUnit_sub _ _ _ u ha
    have hd : (r - ζ.1 ^ a.val) - (r - ζ.1 ^ b.val) = ζ.1 ^ b.val - ζ.1 ^ a.val := by ring
    rw [hd]
    exact (hP q _ ζ).2.1 b a (Ne.symm hab)
  obtain ⟨f0, hf0def⟩ : ∃ f0 : U → ZMod q, f0 = fun u => Classical.choose (hex u) := ⟨_, rfl⟩
  have hf0 : ∀ u, u ∉ U.basicOpen (r - ζ.1 ^ (f0 u).val) := by
    intro u
    rw [hf0def]
    exact Classical.choose_spec (hex u)
  have hf0_iff : ∀ u a, f0 u = a ↔ u ∉ U.basicOpen (r - ζ.1 ^ a.val) := by
    intro u a
    constructor
    · rintro rfl
      exact hf0 u
    · intro ha
      by_contra hne
      exact (hf0 u) (huniq u a (f0 u) (Ne.symm hne) ha)
  have hloc : IsLocallyConstant f0 := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro a
    have hfib : f0 ⁻¹' {a} = ⋂ b ∈ (Finset.univ.erase a : Finset (ZMod q)), (U.basicOpen (r - ζ.1 ^ b.val) : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_erase, Finset.mem_univ,
        and_true, SetLike.mem_coe]
      rw [hf0_iff]
      constructor
      · intro ha b hb
        exact huniq u a b (Ne.symm hb) ha
      · intro h ha
        obtain ⟨a', ha'⟩ := hex u
        by_cases heq : a' = a
        · exact ha' (heq ▸ ha)
        · exact ha' (h a' heq)
    rw [hfib]
    exact isOpen_biInter_finset fun b _ => (U.basicOpen (r - ζ.1 ^ b.val)).isOpen
  refine ⟨⟨f0, hloc⟩, ?_, fun u a ha => (hf0_iff u a).mpr ha⟩
  delta CrystallineSemistableComparison.E.IsPow
  intro V g a hga
  have hunitb : ∀ b : ZMod q, b ≠ a → IsUnit (g.appTop.hom (r - ζ.1 ^ b.val)) := fun b hb =>
    isUnit_appTop_of_mem g _ (fun v => huniq (g v) a b (Ne.symm hb) ((hf0_iff (g v) a).mp (hga v)))
  have hprodV : ∏ b : ZMod q, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val) = 0 := by
    have h0 := congrArg g.appTop.hom hprod
    rw [map_prod, map_zero] at h0
    simpa only [map_sub, map_pow] using h0
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)] at hprodV
  have hu : IsUnit (∏ b ∈ Finset.univ.erase a, (g.appTop.hom r - g.appTop.hom ζ.1 ^ b.val)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one (fun b hb => ?_)
    have h1 := hunitb b (Finset.ne_of_mem_erase hb)
    simpa only [map_sub, map_pow] using h1
  have h0 : g.appTop.hom r - g.appTop.hom ζ.1 ^ a.val = 0 := hu.mul_left_eq_zero.mp hprodV
  show g.appTop.hom r = (g.appTop.hom ζ.1) ^ a.val
  exact sub_eq_zero.mp h0

/- English proof (translation)
Introduce `hP q _ U ζ`. Use `⟨fun r hr => ?_, fun ξ => ?_⟩` and prove the remaining obligations. Take `⟨f, hf, -⟩` from `exists_isPow hP q U ζ r hr`. Conclude with `⟨f, hf⟩`. Establish `hξq : ξ.1 ^ q = 1` using `(hP q _ ξ).1`.

Take `⟨f, hf, hloc⟩` from `exists_isPow hP q U ζ ξ.1 hξq`. Use `⟨f, hf, fun u => ?_⟩` and prove the remaining obligations. Establish `hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0`. Rewrite using `[← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]`. Take `⟨a, -, ha⟩` from `exists_notMem_basicOpen Finset.univ (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u`.

Rewrite using `[hloc u a ha]`. Assume the negation of the conclusion as `hna`. Use `set m := a.val with hm`. Establish `hq : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `ha' : a = (m : ZMod q)` using `(ZMod.natCast_zmod_val a).symm`.

Establish `hcop : ¬ m.Coprime q`. Introduce `hc`. Conclude with `hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)`. Use `set g := Nat.gcd m q with hgdef`. Establish `hg1 : g ≠ 1` using `hcop`.

Establish `hgpos : 0 < g` using `Nat.gcd_pos_of_pos_right m hq`. Establish `hgq : g ∣ q` using `Nat.gcd_dvd_right m q`. Establish `hgm : g ∣ m` using `Nat.gcd_dvd_left m q`. Use `set k := q / g with hkdef`. Establish `hkpos : 0 < k` using `Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos`.

Establish `hklt : k < q` using `Nat.div_lt_self hq (by omega)`. Establish `hζq : ζ.1 ^ q = 1` using `(hP q _ ζ).1`. Establish `hζmk : (ζ.1 ^ m) ^ k = 1`. Take `⟨m', hm'⟩` from `hgm`. Establish `e1 : m * k = q * m'`.

Rewrite using `[hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]`. Rewrite using `[← pow_mul, e1, pow_mul, hζq, one_pow]`. Establish `hunit : IsUnit (ξ.1 ^ k - 1)`. Establish `hne : ((k : ℕ) : ZMod q) ≠ 0`. Rewrite using `[Ne, ZMod.natCast_eq_zero_iff]`.

Introduce `hd`. Conclude with `absurd (Nat.le_of_dvd hkpos hd) (by omega)`. Establish `hu` using `(hP q _ ξ).2.1 (k : ZMod q) 0 hne`. Rewrite `hu` using `[ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero]`. Then use the resulting hypothesis. Establish `hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1`.

Establish `hs` using `sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k`. Rewrite `hs` using `[hζmk]`. Then use the resulting hypothesis. Apply `ha` to reduce the goal to its premises. Rewrite using `[Scheme.mem_basicOpen_top]`. Conclude with `isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)`.
-/
theorem rootPow : CrystallineSemistableComparison.E.PrimAlg → CrystallineSemistableComparison.E.RootPow := by
  intro hP q _ U ζ
  refine ⟨fun r hr => ?_, fun ξ => ?_⟩
  · obtain ⟨f, hf, -⟩ := exists_isPow hP q U ζ r hr
    exact ⟨f, hf⟩
  · have hξq : ξ.1 ^ q = 1 := (hP q _ ξ).1
    obtain ⟨f, hf, hloc⟩ := exists_isPow hP q U ζ ξ.1 hξq
    refine ⟨f, hf, fun u => ?_⟩
    have hprod : ∏ a : ZMod q, (ξ.1 - ζ.1 ^ a.val) = 0 := by
      rw [← (hP q _ ζ).2.2.1 ξ.1, hξq, sub_self]
    obtain ⟨a, -, ha⟩ := exists_notMem_basicOpen Finset.univ
      (fun a : ZMod q => ξ.1 - ζ.1 ^ a.val) hprod u
    rw [hloc u a ha]
    by_contra hna
    set m := a.val with hm
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have ha' : a = (m : ZMod q) := (ZMod.natCast_zmod_val a).symm
    have hcop : ¬ m.Coprime q := by
      intro hc
      exact hna (ha' ▸ (ZMod.isUnit_iff_coprime m q).2 hc)
    set g := Nat.gcd m q with hgdef
    have hg1 : g ≠ 1 := hcop
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_right m hq
    have hgq : g ∣ q := Nat.gcd_dvd_right m q
    have hgm : g ∣ m := Nat.gcd_dvd_left m q
    set k := q / g with hkdef
    have hkpos : 0 < k := Nat.div_pos (Nat.le_of_dvd hq hgq) hgpos
    have hklt : k < q := Nat.div_lt_self hq (by omega)
    have hζq : ζ.1 ^ q = 1 := (hP q _ ζ).1
    have hζmk : (ζ.1 ^ m) ^ k = 1 := by
      obtain ⟨m', hm'⟩ := hgm
      have e1 : m * k = q * m' := by
        rw [hm', hkdef, mul_comm g m', mul_assoc, Nat.mul_div_cancel' hgq, mul_comm]
      rw [← pow_mul, e1, pow_mul, hζq, one_pow]
    have hunit : IsUnit (ξ.1 ^ k - 1) := by
      have hne : ((k : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        exact absurd (Nat.le_of_dvd hkpos hd) (by omega)
      have hu := (hP q _ ξ).2.1 (k : ZMod q) 0 hne
      rwa [ZMod.val_natCast_of_lt hklt, ZMod.val_zero, pow_zero] at hu
    have hdvd : ξ.1 - ζ.1 ^ m ∣ ξ.1 ^ k - 1 := by
      have hs := sub_dvd_pow_sub_pow ξ.1 (ζ.1 ^ m) k
      rwa [hζmk] at hs
    apply ha
    rw [Scheme.mem_basicOpen_top]
    exact isUnit_of_dvd_unit (map_dvd _ hdvd) (hunit.map _)

end GlobalTheory.CompanionTheory.RootPowLC
