import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SmulFinsum

set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Establish `h` using `hχl 0 0 y`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_left_cancel₀ (hχ0 0 y) (h.symm.trans (mul_one _).symm)`. Consider the case `succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]`.
-/
private theorem chi_nsmul_left_eq_pow {χ : W → W → ℂ} (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ (n • s) y = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχl 0 0 y
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 0 y) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχl, ih, pow_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_smul, pow_zero]`. Establish `h` using `hχr s 0 0`. Rewrite `h` using `[add_zero]`.

Conclude with `mul_left_cancel₀ (hχ0 s 0) (h.symm.trans (mul_one _).symm)`. Consider the case `succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]`.
-/
private theorem chi_nsmul_right_eq_pow {χ : W → W → ℂ} (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hχ0 : ∀ t y, χ t y ≠ 0) (s y : W) (n : ℕ) : χ s (n • y) = χ s y ^ n := by
  induction n with
  | zero =>
    rw [zero_smul, pow_zero]
    have h := hχr s 0 0
    rw [add_zero] at h
    exact mul_left_cancel₀ (hχ0 s 0) (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [succ_nsmul, hχr, ih, pow_succ]

/- English proof (translation)
Establish `h` using `QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : W ⧸ S))`. Use `⟨(QuotientAddGroup.mk a : W ⧸ S).out - a, ?_, by abel⟩` and prove the remaining obligations. Establish `h2` using `S.neg_mem h`. Establish `h3 : -(-(QuotientAddGroup.mk a : W ⧸ S).out + a) = (QuotientAddGroup.mk a : W ⧸ S).out - a` using `by abel`. Rewrite `h2` using `[h3]`.

Conclude with `h2`.
-/
theorem mk_out_sub (S : AddSubgroup W) (a : W) : ∃ l ∈ S, (QuotientAddGroup.mk a : W ⧸ S).out = a + l := by
  have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (QuotientAddGroup.mk a : W ⧸ S))
  refine ⟨(QuotientAddGroup.mk a : W ⧸ S).out - a, ?_, by abel⟩
  have h2 := S.neg_mem h
  have h3 : -(-(QuotientAddGroup.mk a : W ⧸ S).out + a) = (QuotientAddGroup.mk a : W ⧸ S).out - a := by abel
  rw [h3] at h2
  exact h2

/- English proof (translation)
Use `Set.finite_coe_iff.mp (Finite.of_injective (fun q : {q : W ⧸ smulSub k H | k • q.out ∈ H} => (QuotientAddGroup.mk (⟨k • q.1.out, q.2⟩ : H) : Qt (k * k) H)) ?_)` and prove the remaining obligations. Introduce and unpack `⟨q₁, h₁⟩ ⟨q₂, h₂⟩ he`. Establish `he'` using `QuotientAddGroup.eq.mp he`. Rewrite `he'` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `hm : k • (-q₁.out + q₂.out) ∈ smulSub (k * k) H`.

Use `he' using 1` and compare the differences between its conclusion and the goal. Simplify using `[smul_add, smul_neg]`. Take `⟨h, hH, hh⟩` from `AddSubgroup.mem_map.mp hm`. Establish `key : -q₁.out + q₂.out = k • h`. Establish `h0 : k • (-q₁.out + q₂.out - k • h) = 0`.

Rewrite using `[smul_sub, smul_smul]`. Conclude with `sub_eq_zero.mpr hh.symm`. Conclude with `sub_eq_zero.mp (htf _ h0)`. Establish `e1` using `QuotientAddGroup.out_eq' q₁`. Establish `e2` using `QuotientAddGroup.out_eq' q₂`.

Use `Subtype.ext (e1.symm.trans (Eq.trans ?_ e2))` and prove the remaining obligations. Conclude with `QuotientAddGroup.eq.mpr (by rw [key]; exact AddSubgroup.mem_map_of_mem _ hH)`.
-/
theorem finite_out_smul (H : AddSubgroup W) {k : ℕ} [Finite (Qt (k * k) H)] (htf : ∀ t : W, k • t = 0 → t = 0) :
    {q : W ⧸ smulSub k H | k • q.out ∈ H}.Finite := by
  refine Set.finite_coe_iff.mp (Finite.of_injective
    (fun q : {q : W ⧸ smulSub k H | k • q.out ∈ H} =>
      (QuotientAddGroup.mk (⟨k • q.1.out, q.2⟩ : H) : Qt (k * k) H)) ?_)
  rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-q₁.out + q₂.out) ∈ smulSub (k * k) H := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨h, hH, hh⟩ := AddSubgroup.mem_map.mp hm
  have key : -q₁.out + q₂.out = k • h := by
    have h0 : k • (-q₁.out + q₂.out - k • h) = 0 := by
      rw [smul_sub, smul_smul]
      exact sub_eq_zero.mpr hh.symm
    exact sub_eq_zero.mp (htf _ h0)
  have e1 := QuotientAddGroup.out_eq' q₁
  have e2 := QuotientAddGroup.out_eq' q₂
  refine Subtype.ext (e1.symm.trans (Eq.trans ?_ e2))
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact AddSubgroup.mem_map_of_mem _ hH)

section Uniq

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}

def Gk (L Y : AddSubgroup W) (k : ℕ) : AddSubgroup (QY L Y) :=
  (Y ⊓ L.comap (nsmulAddMonoidHom k)).map (QuotientAddGroup.mk' (L ⊓ Y))

def Pk (ρ : W → Module.End ℂ V) (L Y : AddSubgroup W) (f₀ : V) (k : ℕ) : V :=
  (Nat.card (Gk L Y k) : ℂ)⁻¹ • ∑ᶠ g : Gk L Y k, ρ ((g : QY L Y).out) f₀

open Classical in

def indk (L X : AddSubgroup W) (k : ℕ) (t : W) : ℂ := if t ∈ smulSub k (L ⊓ X) then 1 else 0

/- English proof (translation)
Take `⟨g, hg⟩` from `g`. Take `⟨y, hy, rfl⟩` from `AddSubgroup.mem_map.mp hg`. Rewrite `hy` using `[AddSubgroup.mem_inf, AddSubgroup.mem_comap]`. Take `⟨l, hl, he⟩` from `mk_out_sub (L ⊓ Y) y`. Express the relevant statement in the definitionally equal form `(QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ Y ∧ k • (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ L`.

Rewrite using `[he]`. Rewrite `hl` using `[AddSubgroup.mem_inf]`. Use `⟨Y.add_mem hy.1 hl.2, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Conclude with `L.add_mem hy.2 (nsmul_mem hl.1 k)`.
-/
theorem Gk_out {k : ℕ} (g : Gk L Y k) : (g : QY L Y).out ∈ Y ∧ k • (g : QY L Y).out ∈ L := by
  obtain ⟨g, hg⟩ := g
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hg
  rw [AddSubgroup.mem_inf, AddSubgroup.mem_comap] at hy
  obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y
  change (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ Y ∧ k • (QuotientAddGroup.mk y : W ⧸ (L ⊓ Y)).out ∈ L
  rw [he]
  rw [AddSubgroup.mem_inf] at hl
  refine ⟨Y.add_mem hy.1 hl.2, ?_⟩
  rw [smul_add]
  exact L.add_mem hy.2 (nsmul_mem hl.1 k)

/- English proof (translation)
Use `haveI := hfinY k hk`. Use `Finite.of_injective (fun g : Gk L Y k => (QuotientAddGroup.mk (⟨k • (g : QY L Y).out, AddSubgroup.mem_inf.mpr ⟨(Gk_out g).2, nsmul_mem (Gk_out g).1 k⟩⟩ : ↥(L ⊓ Y)) : Qt k (L ⊓ Y))) ?_` and prove the remaining obligations. Introduce `g₁ g₂ he`. Establish `he'` using `QuotientAddGroup.eq.mp he`. Rewrite `he'` using `[AddSubgroup.mem_addSubgroupOf]`.

Establish `hm : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out) ∈ smulSub k (L ⊓ Y)`. Use `he' using 1` and compare the differences between its conclusion and the goal. Simplify using `[smul_add, smul_neg]`. Take `⟨m, hmm, hkm⟩` from `AddSubgroup.mem_map.mp hm`. Establish `key : -(g₁ : QY L Y).out + (g₂ : QY L Y).out = m`.

Establish `h0 : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out - m) = 0`. Rewrite using `[smul_sub]`. Conclude with `sub_eq_zero.mpr hkm.symm`. Conclude with `sub_eq_zero.mp (htf k hk _ h0)`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e1` using `QuotientAddGroup.out_eq' (g₁ : QY L Y)`. Establish `e2` using `QuotientAddGroup.out_eq' (g₂ : QY L Y)`. Use `e1.symm.trans (Eq.trans ?_ e2)` and prove the remaining obligations. Conclude with `QuotientAddGroup.eq.mpr (by rw [key]; exact hmm)`.
-/
theorem Gk_finite (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y))) (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)
    {k : ℕ} (hk : 0 < k) : Finite (Gk L Y k) := by
  haveI := hfinY k hk
  refine Finite.of_injective (fun g : Gk L Y k =>
    (QuotientAddGroup.mk (⟨k • (g : QY L Y).out,
      AddSubgroup.mem_inf.mpr ⟨(Gk_out g).2, nsmul_mem (Gk_out g).1 k⟩⟩ : ↥(L ⊓ Y)) : Qt k (L ⊓ Y))) ?_
  intro g₁ g₂ he
  have he' := QuotientAddGroup.eq.mp he
  rw [AddSubgroup.mem_addSubgroupOf] at he'
  have hm : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out) ∈ smulSub k (L ⊓ Y) := by
    convert he' using 1
    simp [smul_add, smul_neg]
  obtain ⟨m, hmm, hkm⟩ := AddSubgroup.mem_map.mp hm
  have key : -(g₁ : QY L Y).out + (g₂ : QY L Y).out = m := by
    have h0 : k • (-(g₁ : QY L Y).out + (g₂ : QY L Y).out - m) = 0 := by
      rw [smul_sub]
      exact sub_eq_zero.mpr hkm.symm
    exact sub_eq_zero.mp (htf k hk _ h0)
  apply Subtype.ext
  have e1 := QuotientAddGroup.out_eq' (g₁ : QY L Y)
  have e2 := QuotientAddGroup.out_eq' (g₂ : QY L Y)
  refine e1.symm.trans (Eq.trans ?_ e2)
  exact QuotientAddGroup.eq.mpr (by rw [key]; exact hmm)

end Uniq

section Uniq2

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχr hLL in
/- English proof (translation)
Establish `hsum : ((g + g' : Gk L Y k) : QY L Y) = QuotientAddGroup.mk ((g : QY L Y).out + (g' : QY L Y).out)`. Rewrite using `[AddSubgroup.coe_add, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']`. Take `⟨l, hl, he⟩` from `mk_out_sub (L ⊓ Y) ((g : QY L Y).out + (g' : QY L Y).out)`. Rewrite using `[hsum, he, hχr, hχr, hLL t ht l hl, mul_one]`.
-/
theorem chi_out_add {k : ℕ} {t : W} (ht : t ∈ L ⊓ X) (g g' : Gk L Y k) :
    χ t ((g + g' : Gk L Y k) : QY L Y).out = χ t (g : QY L Y).out * χ t (g' : QY L Y).out := by
  have hsum : ((g + g' : Gk L Y k) : QY L Y) =
      QuotientAddGroup.mk ((g : QY L Y).out + (g' : QY L Y).out) := by
    rw [AddSubgroup.coe_add, QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) ((g : QY L Y).out + (g' : QY L Y).out)
  rw [hsum, he, hχr, hχr, hLL t ht l hl, mul_one]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
/- English proof (translation)
Use `haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk`. Use `letI : Fintype (Gk L Y k) := Fintype.ofFinite _`. Rewrite using `[finsum_eq_sum_of_fintype]`. Use `split_ifs with hts`. Establish `h1 : ∀ g : Gk L Y k, χ t (g : QY L Y).out = 1`.

Introduce `g`. Take `⟨s, hs, hst⟩` from `AddSubgroup.mem_map.mp hts`. Establish `hst' : t = k • s` using `hst.symm`. Take `⟨hgY, hgL⟩` from `Gk_out g`. Rewrite using `[hst', chi_nsmul_left_eq_pow hχl hχ0, ← chi_nsmul_right_eq_pow hχr hχ0]`.

Conclude with `hLL s hs _ (AddSubgroup.mem_inf.mpr ⟨hgL, nsmul_mem hgY k⟩)`. Rewrite using `[Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]`. Establish `hne : ∃ g : Gk L Y k, χ t (g : QY L Y).out ≠ 1`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Apply `hts` to reduce the goal to its premises. Establish `htX : t ∈ X` using `(AddSubgroup.mem_inf.mp ht).2`. Take `⟨s, hsX, hks⟩` from `hdivX k hk t htX`. Establish `hsL : s ∈ L`. Apply `hdX s hsX` to reduce the goal to its premises.

Introduce `y hy`. Take `⟨y', hy'Y, hky'⟩` from `hdivY k hk y (AddSubgroup.mem_inf.mp hy).2`. Establish `hmem : (QuotientAddGroup.mk y' : QY L Y) ∈ Gk L Y k`. Use `AddSubgroup.mem_map.mpr ⟨y', AddSubgroup.mem_inf.mpr ⟨hy'Y, ?_⟩, rfl⟩` and prove the remaining obligations. Use `show k • y' ∈ L`.

Rewrite using `[hky']`. Conclude with `(AddSubgroup.mem_inf.mp hy).1`. Establish `h1` using `hall ⟨_, hmem⟩`. Take `⟨l, hl, he⟩` from `mk_out_sub (L ⊓ Y) y'`. Establish `h2 : χ t (QuotientAddGroup.mk y' : QY L Y).out = χ t y'`.

Rewrite using `[he, hχr, hLL t ht l hl, mul_one]`. Rewrite using `[← hky', chi_nsmul_right_eq_pow hχr hχ0, ← chi_nsmul_left_eq_pow hχl hχ0, hks, ← h2]`. Conclude with `h1`. Conclude with `AddSubgroup.mem_map.mpr ⟨s, AddSubgroup.mem_inf.mpr ⟨hsL, hsX⟩, hks⟩`. Take `⟨g₀, hg₀⟩` from `hne`.

Establish `hS : ∑ g : Gk L Y k, χ t (g : QY L Y).out = χ t (g₀ : QY L Y).out * ∑ g : Gk L Y k, χ t (g : QY L Y).out`. Rewrite using `[Finset.mul_sum]`. Use `symm`. Use `Fintype.sum_equiv (Equiv.addLeft g₀) _ _ (fun g => ?_)` and prove the remaining obligations. Conclude with `(chi_out_add hχr hLL ht g₀ g).symm`.

Establish `h3 : (1 - χ t (g₀ : QY L Y).out) * ∑ g : Gk L Y k, χ t (g : QY L Y).out = 0`. Rewrite using `[sub_mul, one_mul, ← hS, sub_self]`. Conclude with `(mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hg₀))`.
-/
theorem chi_sum {k : ℕ} (hk : 0 < k) {t : W} (ht : t ∈ L ⊓ X) :
    ∑ᶠ g : Gk L Y k, χ t (g : QY L Y).out =
      if t ∈ smulSub k (L ⊓ X) then (Nat.card (Gk L Y k) : ℂ) else 0 := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hts
  · have h1 : ∀ g : Gk L Y k, χ t (g : QY L Y).out = 1 := by
      intro g
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hts
      have hst' : t = k • s := hst.symm
      obtain ⟨hgY, hgL⟩ := Gk_out g
      rw [hst', chi_nsmul_left_eq_pow hχl hχ0, ← chi_nsmul_right_eq_pow hχr hχ0]
      exact hLL s hs _ (AddSubgroup.mem_inf.mpr ⟨hgL, nsmul_mem hgY k⟩)
    rw [Finset.sum_congr rfl (fun g _ => h1 g), Finset.sum_const, Finset.card_univ,
      Nat.card_eq_fintype_card, nsmul_eq_mul, mul_one]
  · have hne : ∃ g : Gk L Y k, χ t (g : QY L Y).out ≠ 1 := by
      by_contra hall
      push_neg at hall
      apply hts
      have htX : t ∈ X := (AddSubgroup.mem_inf.mp ht).2
      obtain ⟨s, hsX, hks⟩ := hdivX k hk t htX
      have hsL : s ∈ L := by
        apply hdX s hsX
        intro y hy
        obtain ⟨y', hy'Y, hky'⟩ := hdivY k hk y (AddSubgroup.mem_inf.mp hy).2
        have hmem : (QuotientAddGroup.mk y' : QY L Y) ∈ Gk L Y k := by
          refine AddSubgroup.mem_map.mpr ⟨y', AddSubgroup.mem_inf.mpr ⟨hy'Y, ?_⟩, rfl⟩
          show k • y' ∈ L
          rw [hky']
          exact (AddSubgroup.mem_inf.mp hy).1
        have h1 := hall ⟨_, hmem⟩
        obtain ⟨l, hl, he⟩ := mk_out_sub (L ⊓ Y) y'
        have h2 : χ t (QuotientAddGroup.mk y' : QY L Y).out = χ t y' := by
          rw [he, hχr, hLL t ht l hl, mul_one]
        rw [← hky', chi_nsmul_right_eq_pow hχr hχ0, ← chi_nsmul_left_eq_pow hχl hχ0, hks, ← h2]
        exact h1
      exact AddSubgroup.mem_map.mpr ⟨s, AddSubgroup.mem_inf.mpr ⟨hsL, hsX⟩, hks⟩
    obtain ⟨g₀, hg₀⟩ := hne
    have hS : ∑ g : Gk L Y k, χ t (g : QY L Y).out =
        χ t (g₀ : QY L Y).out * ∑ g : Gk L Y k, χ t (g : QY L Y).out := by
      rw [Finset.mul_sum]
      symm
      refine Fintype.sum_equiv (Equiv.addLeft g₀) _ _ (fun g => ?_)
      exact (chi_out_add hχr hLL ht g₀ g).symm
    have h3 : (1 - χ t (g₀ : QY L Y).out) * ∑ g : Gk L Y k, χ t (g : QY L Y).out = 0 := by
      rw [sub_mul, one_mul, ← hS, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr (Ne.symm hg₀))

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
/- English proof (translation)
Use `haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk`. Establish `hcard : (Nat.card (Gk L Y k) : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Unfold `indk`. Distinguish the cases in `htLX : t ∈ L ∧ t ∈ X`. Rewrite using `[if_pos htLX]`.

Simplify using `only [mul_one]`. Rewrite using `[chi_sum hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk (AddSubgroup.mem_inf.mpr htLX)]`. Use `split_ifs`. Conclude with `(inv_mul_cancel₀ hcard).symm`. Simplify using the standard rewrite rules.

Establish `hnot : t ∉ smulSub k (L ⊓ X)`. Introduce `hm`. Take `⟨s, hs, hst⟩` from `AddSubgroup.mem_map.mp hm`. Apply `htLX` to reduce the goal to its premises. Rewrite using `[← hst]`.

Conclude with `AddSubgroup.mem_inf.mp (nsmul_mem hs k)`. Rewrite using `[if_neg hnot, if_neg htLX]`. Simplify using the standard rewrite rules.
-/
theorem indk_eq {k : ℕ} (hk : 0 < k) (t : W) :
    indk L X k t = (Nat.card (Gk L Y k) : ℂ)⁻¹ * ∑ᶠ g : Gk L Y k,
      χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  have hcard : (Nat.card (Gk L Y k) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold indk
  by_cases htLX : t ∈ L ∧ t ∈ X
  · rw [if_pos htLX]
    simp only [mul_one]
    rw [chi_sum hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk (AddSubgroup.mem_inf.mpr htLX)]
    split_ifs
    · exact (inv_mul_cancel₀ hcard).symm
    · simp
  · have hnot : t ∉ smulSub k (L ⊓ X) := by
      intro hm
      obtain ⟨s, hs, hst⟩ := AddSubgroup.mem_map.mp hm
      apply htLX
      rw [← hst]
      exact AddSubgroup.mem_inf.mp (nsmul_mem hs k)
    rw [if_neg hnot, if_neg htLX]
    simp

open Classical in
/- English proof (translation)
Establish `hmem : ∀ t, indk L X k t ≠ 0 → t ∈ L ⊓ X`. Introduce `t ht`. Unfold `indk at ht`. Use `split_ifs at ht with h`. Take `⟨s, hs, rfl⟩` from `AddSubgroup.mem_map.mp h`.

Conclude with `nsmul_mem hs k`. Conclude with `absurd rfl ht`. Use `⟨fun t ht => (AddSubgroup.mem_inf.mp (hmem t ht)).2, k, hk, ?_, fun t ht => nsmul_mem (AddSubgroup.mem_inf.mp (hmem t ht)).1 k⟩` and prove the remaining obligations. Introduce `u hu t`. Establish `hku : k • u ∈ smulSub k (L ⊓ X)` using `AddSubgroup.mem_map_of_mem _ hu`.

Establish `hiff : t + k • u ∈ smulSub k (L ⊓ X) ↔ t ∈ smulSub k (L ⊓ X)` using `(smulSub k (L ⊓ X)).add_mem_cancel_right hku`. Unfold `indk`. Distinguish the cases in `h : t ∈ smulSub k (L ⊓ X)`. Rewrite using `[if_pos (hiff.mpr h), if_pos h]`. Rewrite using `[if_neg (mt hiff.mp h), if_neg h]`.
-/
theorem isSB_indk {k : ℕ} (hk : 0 < k) : IsSB L X (indk L X k) := by
  have hmem : ∀ t, indk L X k t ≠ 0 → t ∈ L ⊓ X := by
    intro t ht
    unfold indk at ht
    split_ifs at ht with h
    · obtain ⟨s, hs, rfl⟩ := AddSubgroup.mem_map.mp h
      exact nsmul_mem hs k
    · exact absurd rfl ht
  refine ⟨fun t ht => (AddSubgroup.mem_inf.mp (hmem t ht)).2, k, hk, ?_,
    fun t ht => nsmul_mem (AddSubgroup.mem_inf.mp (hmem t ht)).1 k⟩
  intro u hu t
  have hku : k • u ∈ smulSub k (L ⊓ X) := AddSubgroup.mem_map_of_mem _ hu
  have hiff : t + k • u ∈ smulSub k (L ⊓ X) ↔ t ∈ smulSub k (L ⊓ X) :=
    (smulSub k (L ⊓ X)).add_mem_cancel_right hku
  unfold indk
  by_cases h : t ∈ smulSub k (L ⊓ X)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf in
open Classical in
/- English proof (translation)
Use `haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk`. Use `letI : Fintype (Gk L Y k) := Fintype.ofFinite _`. Establish `h1 : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0)`. Use `⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`.

Conclude with `ht (if_neg (fun h' => h h'.2))`. Establish `hu'` using `AddSubgroup.mem_inf.mp hu`. Establish `hiff : (t + u ∈ L ∧ t + u ∈ X) ↔ (t ∈ L ∧ t ∈ X)` using `and_congr (L.add_mem_cancel_right hu'.1) (X.add_mem_cancel_right hu'.2)`. Use `show (if t + 1 • u ∈ L ∧ t + 1 • u ∈ X then (1 : ℂ) else 0) = if t ∈ L ∧ t ∈ X then 1 else 0`. Rewrite using `[one_smul]`.

Distinguish the cases in `h : t ∈ L ∧ t ∈ X`. Rewrite using `[if_pos (hiff.mpr h), if_pos h]`. Rewrite using `[if_neg (mt hiff.mp h), if_neg h]`. Rewrite using `[one_smul]`. Assume the negation of the conclusion as `h`.

Conclude with `ht (if_neg (fun h' => h h'.1))`. Establish `hfun : indk L X k = ∑ g : Gk L Y k, ((Nat.card (Gk L Y k) : ℂ)⁻¹ • (fun t => χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0)))`. Use function extensionality and compare the values at `t`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[indk_eq hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk t, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Rewrite using `[hfun, map_sum]`. Simplify using `only [map_smul]`. Unfold `Pk`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun g _ => ?_)` and prove the remaining obligations. Use `congr 1`. Establish `h2` using `hmo _ h1 _ (Gk_out g).1`. Rewrite using `[h2, hva]`.
-/
theorem T_indk (T : (W → ℂ) →ₗ[ℂ] V)
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀) {k : ℕ} (hk : 0 < k) :
    T (indk L X k) = Pk ρ L Y f₀ k := by
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  have h1 : IsSB L X (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) := by
    refine ⟨fun t ht => ?_, 1, one_pos, fun u hu t => ?_, fun t ht => ?_⟩
    · by_contra h
      exact ht (if_neg (fun h' => h h'.2))
    · have hu' := AddSubgroup.mem_inf.mp hu
      have hiff : (t + u ∈ L ∧ t + u ∈ X) ↔ (t ∈ L ∧ t ∈ X) :=
        and_congr (L.add_mem_cancel_right hu'.1) (X.add_mem_cancel_right hu'.2)
      show (if t + 1 • u ∈ L ∧ t + 1 • u ∈ X then (1 : ℂ) else 0) = if t ∈ L ∧ t ∈ X then 1 else 0
      rw [one_smul]
      by_cases h : t ∈ L ∧ t ∈ X
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (mt hiff.mp h), if_neg h]
    · rw [one_smul]
      by_contra h
      exact ht (if_neg (fun h' => h h'.1))
  have hfun : indk L X k = ∑ g : Gk L Y k, ((Nat.card (Gk L Y k) : ℂ)⁻¹ •
      (fun t => χ t (g : QY L Y).out * (if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0))) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [indk_eq hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf hk t, finsum_eq_sum_of_fintype, Finset.mul_sum]
  rw [hfun, map_sum]
  simp only [map_smul]
  unfold Pk
  rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun g _ => ?_)
  congr 1
  have h2 := hmo _ h1 _ (Gk_out g).1
  rw [h2, hva]

end Uniq2

section Uniq3

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdX : ∀ x ∈ X, (∀ y ∈ L ⊓ Y, χ x y = 1) → x ∈ L)
  (hdivX : ∀ k : ℕ, 0 < k → ∀ s ∈ X, ∃ t ∈ X, k • t = s)
  (hdivY : ∀ k : ℕ, 0 < k → ∀ s ∈ Y, ∃ t ∈ Y, k • t = s)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

/- English proof (translation)
Use `haveI := hfinX (k * k) (Nat.mul_pos hk hk)`. Establish `hfin : {q : W ⧸ smulSub k (L ⊓ X) | Φ q.out ≠ 0}.Finite`. Use `(finite_out_smul (L ⊓ X) (htf k hk)).subset ?_` and prove the remaining obligations. Introduce `q hq`. Conclude with `AddSubgroup.mem_inf.mpr ⟨hl _ hq, nsmul_mem (hs _ hq) k⟩`.

Establish `hinv : ∀ t, Φ ((QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = Φ t`. Introduce `t`. Take `⟨l, hl', he⟩` from `mk_out_sub (smulSub k (L ⊓ X)) t`. Take `⟨u, hu, rfl⟩` from `AddSubgroup.mem_map.mp hl'`. Rewrite using `[he]`.

Conclude with `hi u hu t`. Establish `hone : ∀ t, indk L X k (t + -(QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = 1`. Introduce `t`. Take `⟨l, hl', he⟩` from `mk_out_sub (smulSub k (L ⊓ X)) t`. Rewrite using `[he]`.

Unfold `indk`. Apply `if_pos` to reduce the goal to its premises. Establish `h3 : t + -(t + l) = -l` using `by abel`. Rewrite using `[h3]`. Conclude with `neg_mem hl'`.

Establish `hzero : ∀ t (q : W ⧸ smulSub k (L ⊓ X)), q ≠ QuotientAddGroup.mk t → indk L X k (t + -q.out) = 0`. Introduce `t q hq`. Unfold `indk`. Apply `if_neg` to reduce the goal to its premises. Introduce `hm`.

Apply `hq` to reduce the goal to its premises. Rewrite using `[← QuotientAddGroup.out_eq' q]`. Apply `QuotientAddGroup.eq.mpr` to reduce the goal to its premises. Rewrite using `[add_comm]`. Conclude with `hm`.

Establish `hdec : Φ = ∑ q ∈ hfin.toFinset, Φ q.out • (fun t => indk L X k (t + -q.out))`. Use function extensionality and compare the values at `t`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single (QuotientAddGroup.mk t)]`.

Rewrite using `[hone, mul_one, hinv]`. Introduce `q _ hq`. Rewrite using `[hzero t q hq, mul_zero]`. Introduce `hn`. Rewrite using `[hone, mul_one, hinv]`.

Assume the negation of the conclusion as `h0`. Apply `hn` to reduce the goal to its premises. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, hinv]`. Conclude with `h0`. Establish `hX : ∀ q ∈ hfin.toFinset, -q.out ∈ X`.

Introduce `q hq`. Conclude with `neg_mem (hs _ (hfin.mem_toFinset.mp hq))`. Establish `hsub : (Function.support fun q : W ⧸ smulSub k (L ⊓ X) => Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k)) ⊆ ↑hfin.toFinset`. Introduce `q hq`. Rewrite using `[Set.Finite.coe_toFinset, Set.mem_setOf_eq]`.

Introduce `h0`. Apply `hq` to reduce the goal to its premises. Simplify using `only [h0, zero_smul]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub]`. Use `conv_lhs => rw [hdec]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun q hq => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, htr _ (isSB_indk hk) _ (hX q hq), T_indk hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf T hmo hva hk]`.
-/
theorem T_formula (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} {k : ℕ} (hk : 0 < k) (hs : ∀ t, Φ t ≠ 0 → t ∈ X)
    (hi : ∀ u ∈ L ⊓ X, ∀ t, Φ (t + k • u) = Φ t) (hl : ∀ t, Φ t ≠ 0 → k • t ∈ L) :
    T Φ = ∑ᶠ q : W ⧸ smulSub k (L ⊓ X), Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) := by
  haveI := hfinX (k * k) (Nat.mul_pos hk hk)
  have hfin : {q : W ⧸ smulSub k (L ⊓ X) | Φ q.out ≠ 0}.Finite := by
    refine (finite_out_smul (L ⊓ X) (htf k hk)).subset ?_
    intro q hq
    exact AddSubgroup.mem_inf.mpr ⟨hl _ hq, nsmul_mem (hs _ hq) k⟩
  have hinv : ∀ t, Φ ((QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = Φ t := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hl'
    rw [he]
    exact hi u hu t
  have hone : ∀ t, indk L X k (t + -(QuotientAddGroup.mk t : W ⧸ smulSub k (L ⊓ X)).out) = 1 := by
    intro t
    obtain ⟨l, hl', he⟩ := mk_out_sub (smulSub k (L ⊓ X)) t
    rw [he]
    unfold indk
    apply if_pos
    have h3 : t + -(t + l) = -l := by abel
    rw [h3]
    exact neg_mem hl'
  have hzero : ∀ t (q : W ⧸ smulSub k (L ⊓ X)), q ≠ QuotientAddGroup.mk t →
      indk L X k (t + -q.out) = 0 := by
    intro t q hq
    unfold indk
    apply if_neg
    intro hm
    apply hq
    rw [← QuotientAddGroup.out_eq' q]
    apply QuotientAddGroup.eq.mpr
    rw [add_comm]
    exact hm
  have hdec : Φ = ∑ q ∈ hfin.toFinset, Φ q.out • (fun t => indk L X k (t + -q.out)) := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (QuotientAddGroup.mk t)]
    · rw [hone, mul_one, hinv]
    · intro q _ hq
      rw [hzero t q hq, mul_zero]
    · intro hn
      rw [hone, mul_one, hinv]
      by_contra h0
      apply hn
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, hinv]
      exact h0
  have hX : ∀ q ∈ hfin.toFinset, -q.out ∈ X := by
    intro q hq
    exact neg_mem (hs _ (hfin.mem_toFinset.mp hq))
  have hsub : (Function.support fun q : W ⧸ smulSub k (L ⊓ X) =>
      Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k)) ⊆ ↑hfin.toFinset := by
    intro q hq
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h0
    apply hq
    simp only [h0, zero_smul]
  rw [finsum_eq_sum_of_support_subset _ hsub]
  conv_lhs => rw [hdec]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  rw [map_smul, htr _ (isSB_indk hk) _ (hX q hq),
    T_indk hχl hχr hχ0 hLL hdX hdivX hdivY hfinY htf T hmo hva hk]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `hΦ`. Rewrite using `[T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T' htr' hmo' hva' hk hs hi hl, T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]`.
-/
theorem model_unique (T T' : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    (htr' : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T' (fun t => Φ (t + x)) = ρ x (T' Φ))
    (hmo' : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T' (fun t => χ t y * Φ t) = ρ y (T' Φ))
    (hva' : T' (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) : T' Φ = T Φ := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  rw [T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T' htr' hmo' hva' hk hs hi hl,
    T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]

include hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf in
open Classical in

/- English proof (translation)
Take `⟨hs, k, hk, hi, hl⟩` from `hΦ`. Use `haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk`. Use `letI : Fintype (Gk L Y k) := Fintype.ofFinite _`. Rewrite using `[T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]`. Use `finsum_induction (fun v => v ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)}) (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) (fun q => ?_)` and prove the remaining obligations.

Use `show Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) ∈ _`. Distinguish the cases in `h0 : Φ q.out = 0`. Rewrite using `[h0, zero_smul]`. Conclude with `Submodule.zero_mem _`. Apply `Submodule.smul_mem` to reduce the goal to its premises.

Unfold `Pk`. Rewrite using `[map_smul, finsum_eq_sum_of_fintype, map_sum]`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.sum_mem` to reduce the goal to its premises. Introduce `g _`.

Conclude with `Submodule.subset_span ⟨-q.out, neg_mem (hs _ h0), (g : QY L Y).out, (Gk_out g).1, rfl⟩`.
-/
theorem model_mem_span (T : (W → ℂ) →ₗ[ℂ] V)
    (htr : ∀ Φ, IsSB L X Φ → ∀ x ∈ X, T (fun t => Φ (t + x)) = ρ x (T Φ))
    (hmo : ∀ Φ, IsSB L X Φ → ∀ y ∈ Y, T (fun t => χ t y * Φ t) = ρ y (T Φ))
    (hva : T (fun t => if t ∈ L ∧ t ∈ X then (1 : ℂ) else 0) = f₀)
    {Φ : W → ℂ} (hΦ : IsSB L X Φ) :
    T Φ ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)} := by
  obtain ⟨hs, k, hk, hi, hl⟩ := hΦ
  haveI : Finite (Gk L Y k) := Gk_finite hfinY htf hk
  letI : Fintype (Gk L Y k) := Fintype.ofFinite _
  rw [T_formula hχl hχr hχ0 hLL hdX hdivX hdivY hfinX hfinY htf T htr hmo hva hk hs hi hl]
  refine finsum_induction (fun v => v ∈ Submodule.span ℂ {v | ∃ a ∈ X, ∃ y ∈ Y, v = ρ a (ρ y f₀)})
    (Submodule.zero_mem _) (fun _ _ => Submodule.add_mem _) (fun q => ?_)
  show Φ q.out • ρ (-q.out) (Pk ρ L Y f₀ k) ∈ _
  by_cases h0 : Φ q.out = 0
  · rw [h0, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    unfold Pk
    rw [map_smul, finsum_eq_sum_of_fintype, map_sum]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro g _
    exact Submodule.subset_span ⟨-q.out, neg_mem (hs _ h0), (g : QY L Y).out, (Gk_out g).1, rfl⟩

end Uniq3

end Formalism.IndefR.Fin.Four

end
