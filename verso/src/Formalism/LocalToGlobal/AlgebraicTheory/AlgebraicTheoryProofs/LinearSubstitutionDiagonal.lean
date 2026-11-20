import Formalism.LocalToGlobal.AlgebraicTheory.DefsKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.AlgTh

open Formalism.L2.Th1.H (matH IsLat IsReps opU sumU taylorMv relIdx imgLat repsExist)
open Formalism.L2.Th1.G (linSub)

namespace KerA

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_killIn {m : ℂ} {L M : AddSubgroup V} {y : V} : y ∈ killIn m L M ↔ y ∈ L ∧ m • y ∈ M := by
  exact Iff.rfl

/- English proof (translation)
Conclude with `Nat.cast_smul_eq_nsmul ℂ m y`.
-/
theorem natCast_smul (m : ℕ) (y : V) : ((m : ℂ)) • y = m • y := by exact Nat.cast_smul_eq_nsmul ℂ m y

/- English proof (translation)
Establish `hg : (Nat.gcdA m₁ m₂) * (m₁ : ℤ) + (Nat.gcdB m₁ m₂) * (m₂ : ℤ) = 1`. Establish `h` using `Nat.gcd_eq_gcd_ab m₁ m₂`. Rewrite `h` using `[hcop.gcd_eq_one]`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1' : ((m₁ : ℤ)) • w ∈ Λ` using `by rw [natCast_zsmul, ← natCast_smul]; exact h1`. Establish `h2' : ((m₂ : ℤ)) • w ∈ Λ` using `by rw [natCast_zsmul, ← natCast_smul]; exact h2`. Establish `hw : w = (Nat.gcdA m₁ m₂) • (((m₁ : ℤ)) • w) + (Nat.gcdB m₁ m₂) • (((m₂ : ℤ)) • w)`. Rewrite using `[smul_smul, smul_smul, ← add_smul, hg, one_smul]`. Rewrite using `[hw]`.

Conclude with `Λ.add_mem (Λ.zsmul_mem h1' _) (Λ.zsmul_mem h2' _)`.
-/
theorem mem_of_coprime {Λ : AddSubgroup V} {m₁ m₂ : ℕ} (hcop : Nat.Coprime m₁ m₂) {w : V}
    (h1 : ((m₁ : ℂ)) • w ∈ Λ) (h2 : ((m₂ : ℂ)) • w ∈ Λ) : w ∈ Λ := by
  have hg : (Nat.gcdA m₁ m₂) * (m₁ : ℤ) + (Nat.gcdB m₁ m₂) * (m₂ : ℤ) = 1 := by
    have h := Nat.gcd_eq_gcd_ab m₁ m₂
    rw [hcop.gcd_eq_one] at h
    push_cast at h
    linarith
  have h1' : ((m₁ : ℤ)) • w ∈ Λ := by rw [natCast_zsmul, ← natCast_smul]; exact h1
  have h2' : ((m₂ : ℤ)) • w ∈ Λ := by rw [natCast_zsmul, ← natCast_smul]; exact h2
  have hw : w = (Nat.gcdA m₁ m₂) • (((m₁ : ℤ)) • w) + (Nat.gcdB m₁ m₂) • (((m₂ : ℤ)) • w) := by
    rw [smul_smul, smul_smul, ← add_smul, hg, one_smul]
  rw [hw]
  exact Λ.add_mem (Λ.zsmul_mem h1' _) (Λ.zsmul_mem h2' _)

/- English proof (translation)
Establish `cz : ∀ (k : ℕ) (y : V), ((k : ℂ)) • y = ((k : ℤ)) • y` using `fun k y => by`. Rewrite using `[natCast_smul, natCast_zsmul]`. Establish `km : ∀ (k : ℕ) {y : V}, y ∈ killIn (k : ℂ) B Λ ↔ y ∈ B ∧ ((k : ℤ)) • y ∈ Λ`. Introduce `k y`. Rewrite using `[mem_killIn, cz]`.

Take `⟨hS1B, hS1d, hS1c⟩` from `h1`. Take `⟨hS2B, hS2d, hS2c⟩` from `h2`. Establish `sep : ∀ a ∈ S₁, ∀ b ∈ S₂, ∀ a' ∈ S₁, ∀ b' ∈ S₂, (a + b) - (a' + b') ∈ Λ → a = a' ∧ b = b'`. Introduce `a ha b hb a' ha' b' hb' h`. Establish `hA` using `(km m₁).1 (hS1B a ha)`.

Establish `hA'` using `(km m₁).1 (hS1B a' ha')`. Establish `hB` using `(km m₂).1 (hS2B b hb)`. Establish `hB'` using `(km m₂).1 (hS2B b' hb')`. Establish `hsum : (a - a') + (b - b') ∈ Λ`. Establish `e : (a + b) - (a' + b') = (a - a') + (b - b')` using `by abel`.

Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `h1d : ((m₁ : ℤ)) • (a - a') ∈ Λ`. Rewrite using `[zsmul_sub]`. Conclude with `Λ.sub_mem hA.2 hA'.2`. Establish `h2d : ((m₂ : ℤ)) • (b - b') ∈ Λ`.

Rewrite using `[zsmul_sub]`. Conclude with `Λ.sub_mem hB.2 hB'.2`. Establish `h1e : ((m₁ : ℤ)) • (b - b') ∈ Λ`. Establish `e : ((m₁ : ℤ)) • (b - b') = ((m₁ : ℤ)) • ((a - a') + (b - b')) - ((m₁ : ℤ)) • (a - a')`. Rewrite using `[smul_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `Λ.sub_mem (Λ.zsmul_mem hsum _) h1d`. Establish `hbΛ : b - b' ∈ Λ` using `mem_of_coprime hcop (by rw [cz]; exact h1e) (by rw [cz]; exact h2d)`. Establish `haΛ : a - a' ∈ Λ`.

Establish `e : a - a' = ((a - a') + (b - b')) - (b - b')` using `by abel`. Rewrite using `[e]`. Conclude with `Λ.sub_mem hsum hbΛ`. Conclude with `⟨hS1d a ha a' ha' haΛ, hS2d b hb b' hb' hbΛ⟩`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨hq1, hq2⟩` from `Finset.mem_product.1 hq`. Conclude with `B.add_mem ((km m₁).1 (hS1B _ hq1)).1 ((km m₂).1 (hS2B _ hq2)).1`. Introduce `x hx y hy hxy`.

Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨r, hr, rfl⟩` from `Finset.mem_image.1 hy`. Take `⟨hq1, hq2⟩` from `Finset.mem_product.1 hq`. Take `⟨hr1, hr2⟩` from `Finset.mem_product.1 hr`. Take `⟨e1, e2⟩` from `sep _ hq1 _ hq2 _ hr1 _ hr2 hxy`.

Use `show q.1 + q.2 = r.1 + r.2`. Rewrite using `[e1, e2]`. Introduce `y hy`. Establish `hg : (Nat.gcdA m₁ m₂) * (m₁ : ℤ) + (Nat.gcdB m₁ m₂) * (m₂ : ℤ) = 1`. Establish `h` using `Nat.gcd_eq_gcd_ab m₁ m₂`.

Rewrite `h` using `[hcop.gcd_eq_one]`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hky : ((m₁ : ℤ) * (m₂ : ℤ)) • y ∈ Λ`. Establish `h` using `hkill y hy`.

Rewrite `h` using `[cz]`. Move the coercions through the operations in `at h`. Conclude with `h`. Establish `hu : ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y ∈ killIn (m₁ : ℂ) B Λ`. Rewrite using `[km]`.

Use `⟨B.zsmul_mem hy _, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, show (m₁ : ℤ) * ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) = (Nat.gcdB m₁ m₂) * ((m₁ : ℤ) * (m₂ : ℤ)) by ring, ← smul_smul]`. Conclude with `Λ.zsmul_mem hky _`. Establish `hv : ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y ∈ killIn (m₂ : ℂ) B Λ`. Rewrite using `[km]`.

Use `⟨B.zsmul_mem hy _, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, show (m₂ : ℤ) * ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) = (Nat.gcdA m₁ m₂) * ((m₁ : ℤ) * (m₂ : ℤ)) by ring, ← smul_smul]`. Conclude with `Λ.zsmul_mem hky _`. Take `⟨y₁, hy₁, d₁⟩` from `hS1c _ hu`. Take `⟨y₂, hy₂, d₂⟩` from `hS2c _ hv`.

Use `⟨y₁ + y₂, Finset.mem_image.2 ⟨(y₁, y₂), Finset.mem_product.2 ⟨hy₁, hy₂⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hsplit : ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y + ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y = y`. Rewrite using `[← add_smul, show (Nat.gcdB m₁ m₂) * (m₂ : ℤ) + (Nat.gcdA m₁ m₂) * (m₁ : ℤ) = 1 by linarith, one_smul]`. Establish `e : y - (y₁ + y₂) = (((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y - y₁) + (((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y - y₂)`. Rewrite using `[sub_add_sub_comm, hsplit]`.

Rewrite using `[e]`. Conclude with `Λ.add_mem d₁ d₂`. Introduce `q hq r hr hqr`. Rewrite `hq`, `hr` using `[Finset.coe_product, Set.mem_prod]`. Establish `hqr' : q.1 + q.2 = r.1 + r.2` using `hqr`.

Establish `h0 : (q.1 + q.2) - (r.1 + r.2) ∈ Λ`. Rewrite using `[hqr', sub_self]`. Conclude with `Λ.zero_mem`. Take `⟨e1, e2⟩` from `sep _ hq.1 _ hq.2 _ hr.1 _ hr.2 h0`. Conclude with `Prod.ext e1 e2`.
-/
theorem image_reps [DecidableEq V] (B Λ : AddSubgroup V) (m₁ m₂ : ℕ) (hcop : Nat.Coprime m₁ m₂)
    (hkill : ∀ y ∈ B, (((m₁ * m₂ : ℕ) : ℂ)) • y ∈ Λ) (S₁ S₂ : Finset V)
    (h1 : IsReps Λ (killIn (m₁ : ℂ) B Λ) S₁) (h2 : IsReps Λ (killIn (m₂ : ℂ) B Λ) S₂) :
    IsReps Λ B ((S₁ ×ˢ S₂).image fun q => q.1 + q.2) ∧ Set.InjOn (fun q : V × V => q.1 + q.2) ↑(S₁ ×ˢ S₂) := by
  have cz : ∀ (k : ℕ) (y : V), ((k : ℂ)) • y = ((k : ℤ)) • y := fun k y => by
    rw [natCast_smul, natCast_zsmul]
  have km : ∀ (k : ℕ) {y : V}, y ∈ killIn (k : ℂ) B Λ ↔ y ∈ B ∧ ((k : ℤ)) • y ∈ Λ := by
    intro k y
    rw [mem_killIn, cz]
  obtain ⟨hS1B, hS1d, hS1c⟩ := h1
  obtain ⟨hS2B, hS2d, hS2c⟩ := h2
  have sep : ∀ a ∈ S₁, ∀ b ∈ S₂, ∀ a' ∈ S₁, ∀ b' ∈ S₂, (a + b) - (a' + b') ∈ Λ → a = a' ∧ b = b' := by
    intro a ha b hb a' ha' b' hb' h
    have hA := (km m₁).1 (hS1B a ha)
    have hA' := (km m₁).1 (hS1B a' ha')
    have hB := (km m₂).1 (hS2B b hb)
    have hB' := (km m₂).1 (hS2B b' hb')
    have hsum : (a - a') + (b - b') ∈ Λ := by
      have e : (a + b) - (a' + b') = (a - a') + (b - b') := by abel
      rwa [e] at h
    have h1d : ((m₁ : ℤ)) • (a - a') ∈ Λ := by
      rw [zsmul_sub]
      exact Λ.sub_mem hA.2 hA'.2
    have h2d : ((m₂ : ℤ)) • (b - b') ∈ Λ := by
      rw [zsmul_sub]
      exact Λ.sub_mem hB.2 hB'.2
    have h1e : ((m₁ : ℤ)) • (b - b') ∈ Λ := by
      have e : ((m₁ : ℤ)) • (b - b') = ((m₁ : ℤ)) • ((a - a') + (b - b')) - ((m₁ : ℤ)) • (a - a') := by
        rw [smul_add]
        abel
      rw [e]
      exact Λ.sub_mem (Λ.zsmul_mem hsum _) h1d
    have hbΛ : b - b' ∈ Λ := mem_of_coprime hcop (by rw [cz]; exact h1e) (by rw [cz]; exact h2d)
    have haΛ : a - a' ∈ Λ := by
      have e : a - a' = ((a - a') + (b - b')) - (b - b') := by abel
      rw [e]
      exact Λ.sub_mem hsum hbΛ
    exact ⟨hS1d a ha a' ha' haΛ, hS2d b hb b' hb' hbΛ⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    exact B.add_mem ((km m₁).1 (hS1B _ hq1)).1 ((km m₂).1 (hS2B _ hq2)).1
  · intro x hx y hy hxy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.1 hq
    obtain ⟨hr1, hr2⟩ := Finset.mem_product.1 hr
    obtain ⟨e1, e2⟩ := sep _ hq1 _ hq2 _ hr1 _ hr2 hxy
    show q.1 + q.2 = r.1 + r.2
    rw [e1, e2]
  · intro y hy
    have hg : (Nat.gcdA m₁ m₂) * (m₁ : ℤ) + (Nat.gcdB m₁ m₂) * (m₂ : ℤ) = 1 := by
      have h := Nat.gcd_eq_gcd_ab m₁ m₂
      rw [hcop.gcd_eq_one] at h
      push_cast at h
      linarith
    have hky : ((m₁ : ℤ) * (m₂ : ℤ)) • y ∈ Λ := by
      have h := hkill y hy
      rw [cz] at h
      push_cast at h
      exact h
    have hu : ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y ∈ killIn (m₁ : ℂ) B Λ := by
      rw [km]
      refine ⟨B.zsmul_mem hy _, ?_⟩
      rw [smul_smul, show (m₁ : ℤ) * ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) = (Nat.gcdB m₁ m₂) * ((m₁ : ℤ) * (m₂ : ℤ)) by ring,
        ← smul_smul]
      exact Λ.zsmul_mem hky _
    have hv : ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y ∈ killIn (m₂ : ℂ) B Λ := by
      rw [km]
      refine ⟨B.zsmul_mem hy _, ?_⟩
      rw [smul_smul, show (m₂ : ℤ) * ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) = (Nat.gcdA m₁ m₂) * ((m₁ : ℤ) * (m₂ : ℤ)) by ring,
        ← smul_smul]
      exact Λ.zsmul_mem hky _
    obtain ⟨y₁, hy₁, d₁⟩ := hS1c _ hu
    obtain ⟨y₂, hy₂, d₂⟩ := hS2c _ hv
    refine ⟨y₁ + y₂, Finset.mem_image.2 ⟨(y₁, y₂), Finset.mem_product.2 ⟨hy₁, hy₂⟩, rfl⟩, ?_⟩
    have hsplit : ((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y + ((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y = y := by
      rw [← add_smul, show (Nat.gcdB m₁ m₂) * (m₂ : ℤ) + (Nat.gcdA m₁ m₂) * (m₁ : ℤ) = 1 by linarith, one_smul]
    have e : y - (y₁ + y₂) = (((Nat.gcdB m₁ m₂) * (m₂ : ℤ)) • y - y₁) + (((Nat.gcdA m₁ m₂) * (m₁ : ℤ)) • y - y₂) := by
      rw [sub_add_sub_comm, hsplit]
    rw [e]
    exact Λ.add_mem d₁ d₂
  · intro q hq r hr hqr
    rw [Finset.coe_product, Set.mem_prod] at hq hr
    have hqr' : q.1 + q.2 = r.1 + r.2 := hqr
    have h0 : (q.1 + q.2) - (r.1 + r.2) ∈ Λ := by
      rw [hqr', sub_self]
      exact Λ.zero_mem
    obtain ⟨e1, e2⟩ := sep _ hq.1 _ hq.2 _ hr.1 _ hr.2 h0
    exact Prod.ext e1 e2

end KerA

open KerA

/- English proof (translation)
Take `⟨hS2, hSd, hSc⟩` from `hS`. Set `φ : S → ↥Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂` to `fun x => QuotientAddGroup.mk ⟨x.1, hS2 x.1 x.2⟩`. Establish `hφ : Function.Bijective φ`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`.

Establish `h` using `(QuotientAddGroup.eq).1 hxy`. Rewrite `h` using `[AddSubgroup.mem_addSubgroupOf]`. Establish `h' : (y : V) - x ∈ Λ₁` using `by simpa [neg_add_eq_sub] using h`. Conclude with `Subtype.ext (hSd y.1 y.2 x.1 x.2 h').symm`. Introduce `c`.

Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective c`. Take `⟨x, hx, hzx⟩` from `hSc z.1 z.2`. Use `⟨⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Apply `(QuotientAddGroup.eq).2` to reduce the goal to its premises. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`.

Simplify `hzx` using `[neg_add_eq_sub]`. Rewrite using `[← Nat.card_eq_of_bijective φ hφ, Nat.card_eq_fintype_card, Fintype.card_coe]`.
-/
private theorem card_quotient_eq_card_of_isReps {V : Type*} [AddCommGroup V] [Module ℂ V] {Λ₁ Λ₂ : AddSubgroup V}
    {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) : Nat.card (↥Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) = S.card := by
  classical
  obtain ⟨hS2, hSd, hSc⟩ := hS
  let φ : S → ↥Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂ := fun x => QuotientAddGroup.mk ⟨x.1, hS2 x.1 x.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      have h := (QuotientAddGroup.eq).1 hxy
      rw [AddSubgroup.mem_addSubgroupOf] at h
      have h' : (y : V) - x ∈ Λ₁ := by simpa [neg_add_eq_sub] using h
      exact Subtype.ext (hSd y.1 y.2 x.1 x.2 h').symm
    · intro c
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective c
      obtain ⟨x, hx, hzx⟩ := hSc z.1 z.2
      refine ⟨⟨x, hx⟩, ?_⟩
      apply (QuotientAddGroup.eq).2
      rw [AddSubgroup.mem_addSubgroupOf]
      simpa [neg_add_eq_sub] using hzx
  rw [← Nat.card_eq_of_bijective φ hφ, Nat.card_eq_fintype_card, Fintype.card_coe]

/- English proof (translation)
Introduce `V _ _ B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2`. Take `⟨hR, hinj⟩` from `KerA.image_reps B Λ m₁ m₂ hcop hkill S₁ S₂ h1 h2`. Rewrite using `[← card_quotient_eq_card_of_isReps hB, card_quotient_eq_card_of_isReps hR, Finset.card_image_of_injOn hinj, Finset.card_product]`.
-/
theorem RepsSplit_card : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B Λ : AddSubgroup V) (m₁ m₂ : ℕ), Nat.Coprime m₁ m₂ →
    (∀ y ∈ B, (((m₁ * m₂ : ℕ) : ℂ)) • y ∈ Λ) →
  ∀ SB S₁ S₂ : Finset V, IsReps Λ B SB → IsReps Λ (killIn (m₁ : ℂ) B Λ) S₁ → IsReps Λ (killIn (m₂ : ℂ) B Λ) S₂ →
    SB.card = S₁.card * S₂.card := by
  intro V _ _ B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2
  classical
  obtain ⟨hR, hinj⟩ := KerA.image_reps B Λ m₁ m₂ hcop hkill S₁ S₂ h1 h2
  rw [← card_quotient_eq_card_of_isReps hB, card_quotient_eq_card_of_isReps hR, Finset.card_image_of_injOn hinj, Finset.card_product]

/- English proof (translation)
Introduce `n _ Λ hL p hp π hπ hπΛ hπ'Λ Sa hSa`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Apply `hp0` to reduce the goal to its premises.

Rewrite using `[← hπ]`. Simplify using the standard rewrite rules. Establish `hπ'0 : conj π ≠ 0`. Rewrite using `[ne_eq, map_eq_zero]`. Conclude with `hπ0`.

Establish `hr1 : π / conj π * (conj π / π) = 1` using `by field_simp`. Establish `hr2 : π / conj π * conj π = π` using `div_mul_cancel₀ _ hπ'0`. Establish `hr3 : conj π / π * π = conj π` using `div_mul_cancel₀ _ hπ0`. Take `⟨hA1, hA2, hA3⟩` from `hSa`. Establish `hinj : Function.Injective (fun x : n → ℂ => (π / conj π) • x)` using `smul_right_injective _ (div_ne_zero hπ0 hπ'0)`.

Establish `hSb : IsReps (cLat π Λ) Λ (Sa.image fun x => (π / conj π) • x)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.1 hx`. Take `⟨w, hw, rfl⟩` from `SC.mem_cLat.1 (hA1 a ha)`.

Use `show (π / conj π) • ((conj π / π) • w) ∈ Λ`. Rewrite using `[smul_smul, hr1, one_smul]`. Conclude with `hw`. Introduce `x hx y hy hxy`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨b, hb, rfl⟩` from `Finset.mem_image.1 hy`. Take `⟨w, hw, hwe⟩` from `SC.mem_cLat.1 hxy`. Establish `hab : a - b ∈ cLat (conj π) Λ`. Use `SC.mem_cLat.2 ⟨w, hw, ?_⟩` and prove the remaining obligations. Establish `e : a - b = (conj π / π) • ((π / conj π) • a - (π / conj π) • b)`.

Rewrite using `[smul_sub, smul_smul, smul_smul, mul_comm (conj π / π) (π / conj π), hr1, one_smul, one_smul]`. Rewrite using `[e, ← hwe, smul_smul, hr3]`. Use `show (π / conj π) • a = (π / conj π) • b`. Rewrite using `[hA2 a ha b hb hab]`. Introduce `y hy`.

Establish `hy' : (conj π / π) • y ∈ cLat (conj π / π) Λ` using `SC.mem_cLat.2 ⟨y, hy, rfl⟩`. Take `⟨a, ha, hd⟩` from `hA3 _ hy'`. Take `⟨w, hw, hwe⟩` from `SC.mem_cLat.1 hd`. Use `⟨(π / conj π) • a, Finset.mem_image.2 ⟨a, ha, rfl⟩, SC.mem_cLat.2 ⟨w, hw, ?_⟩⟩` and prove the remaining obligations. Establish `e : y - (π / conj π) • a = (π / conj π) • ((conj π / π) • y - a)`.

Rewrite using `[smul_sub, smul_smul, hr1, one_smul]`. Rewrite using `[e, ← hwe, smul_smul, hr2]`. Establish `hcard` using `Finset.card_image_of_injective Sa hinj`. Establish `hidx` using `SC.relIdx_cLat Λ hL π hπ0 hπΛ`. Establish `hns : Complex.normSq π = p`.

Establish `h` using `Complex.mul_conj π`. Rewrite `h` using `[hπ]`. Conclude with `h.symm` after adjusting the coercions. Rewrite `hidx` using `[hns]`. Establish `hrel : relIdx (cLat π Λ) Λ = (Sa.image fun x => (π / conj π) • x).card`.

Rewrite using `[← card_quotient_eq_card_of_isReps hSb]`. Both sides reduce to the same expression. Rewrite using `[← hcard, ← hrel]`. Conclude with `hidx` after adjusting the coercions.
-/
theorem index_product_formula : IdxPi := by
  intro n _ Λ hL p hp π hπ hπΛ hπ'Λ Sa hSa
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    apply hp0
    rw [← hπ]
    simp
  have hπ'0 : conj π ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact hπ0
  have hr1 : π / conj π * (conj π / π) = 1 := by field_simp
  have hr2 : π / conj π * conj π = π := div_mul_cancel₀ _ hπ'0
  have hr3 : conj π / π * π = conj π := div_mul_cancel₀ _ hπ0
  obtain ⟨hA1, hA2, hA3⟩ := hSa
  classical
  have hinj : Function.Injective (fun x : n → ℂ => (π / conj π) • x) :=
    smul_right_injective _ (div_ne_zero hπ0 hπ'0)
  have hSb : IsReps (cLat π Λ) Λ (Sa.image fun x => (π / conj π) • x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨w, hw, rfl⟩ := SC.mem_cLat.1 (hA1 a ha)
      show (π / conj π) • ((conj π / π) • w) ∈ Λ
      rw [smul_smul, hr1, one_smul]
      exact hw
    · intro x hx y hy hxy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨w, hw, hwe⟩ := SC.mem_cLat.1 hxy
      have hab : a - b ∈ cLat (conj π) Λ := by
        refine SC.mem_cLat.2 ⟨w, hw, ?_⟩
        have e : a - b = (conj π / π) • ((π / conj π) • a - (π / conj π) • b) := by
          rw [smul_sub, smul_smul, smul_smul, mul_comm (conj π / π) (π / conj π), hr1, one_smul, one_smul]
        rw [e, ← hwe, smul_smul, hr3]
      show (π / conj π) • a = (π / conj π) • b
      rw [hA2 a ha b hb hab]
    · intro y hy
      have hy' : (conj π / π) • y ∈ cLat (conj π / π) Λ := SC.mem_cLat.2 ⟨y, hy, rfl⟩
      obtain ⟨a, ha, hd⟩ := hA3 _ hy'
      obtain ⟨w, hw, hwe⟩ := SC.mem_cLat.1 hd
      refine ⟨(π / conj π) • a, Finset.mem_image.2 ⟨a, ha, rfl⟩, SC.mem_cLat.2 ⟨w, hw, ?_⟩⟩
      have e : y - (π / conj π) • a = (π / conj π) • ((conj π / π) • y - a) := by
        rw [smul_sub, smul_smul, hr1, one_smul]
      rw [e, ← hwe, smul_smul, hr2]
  have hcard := Finset.card_image_of_injective Sa hinj
  have hidx := SC.relIdx_cLat Λ hL π hπ0 hπΛ
  have hns : Complex.normSq π = p := by
    have h := Complex.mul_conj π
    rw [hπ] at h
    exact_mod_cast h.symm
  rw [hns] at hidx
  have hrel : relIdx (cLat π Λ) Λ = (Sa.image fun x => (π / conj π) • x).card := by
    rw [← card_quotient_eq_card_of_isReps hSb]
    rfl
  rw [← hcard, ← hrel]
  exact_mod_cast hidx

/- English proof (translation)
Introduce `K _ n _ _ d F m`. Establish `h : (fun i => (∑ x, MvPowerSeries.C (if i = x then d x else 0) * MvPowerSeries.X x : MvPowerSeries n K)) = d • MvPowerSeries.X`. Use function extensionality and compare the values at `i`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[MvPowerSeries.smul_eq_C_mul]`.

Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i) hi`. Unfold `linSub`.

Rewrite using `[h, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale]`.
-/
theorem linear_substitution_diagonal : LinSubDiag := by
  intro K _ n _ _ d F m
  have h : (fun i => (∑ x, MvPowerSeries.C (if i = x then d x else 0) * MvPowerSeries.X x :
      MvPowerSeries n K)) = d • MvPowerSeries.X := by
    funext i
    rw [Finset.sum_eq_single i]
    · simp [MvPowerSeries.smul_eq_C_mul]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  unfold linSub
  rw [h, ← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale]

namespace KerA

/- English proof (translation)
Establish `hcq` using `card_quotient_eq_card_of_isReps hS`. Establish `hne : S.card ≠ 0`. Take `⟨x, hx, _⟩` from `hS.2.2 0 (killIn (m : ℂ) B Λ).zero_mem`. Conclude with `Finset.card_ne_zero_of_mem hx`. Establish `: Finite (↥(killIn (m : ℂ) B Λ) ⧸ Λ.addSubgroupOf (killIn (m : ℂ) B Λ))` using `Nat.finite_of_card_ne_zero (by rw [hcq]; exact hne)`.

Use `Fact.mk hq` as an intermediate fact. Take `⟨g, hg⟩` from `exists_prime_addOrderOf_dvd_card' q (by rw [hcq]; exact hd)`. Rewrite using `[← hg]`. Apply `addOrderOf_dvd_of_nsmul_eq_zero` to reduce the goal to its premises. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk_surjective g`.

Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul]`. Establish `h` using `(mem_killIn.1 z.2).2`. Rewrite `h` using `[natCast_smul]`. Then use the resulting hypothesis.
-/
theorem card_dvd_prime {V : Type*} [AddCommGroup V] [Module ℂ V] (B Λ : AddSubgroup V) (m : ℕ) (S : Finset V)
    (hS : IsReps Λ (killIn (m : ℂ) B Λ) S) (q : ℕ) (hq : q.Prime) (hd : q ∣ S.card) : q ∣ m := by
  classical
  have hcq := card_quotient_eq_card_of_isReps hS
  have hne : S.card ≠ 0 := by
    obtain ⟨x, hx, _⟩ := hS.2.2 0 (killIn (m : ℂ) B Λ).zero_mem
    exact Finset.card_ne_zero_of_mem hx
  have : Finite (↥(killIn (m : ℂ) B Λ) ⧸ Λ.addSubgroupOf (killIn (m : ℂ) B Λ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcq]; exact hne)
  have := Fact.mk hq
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' q (by rw [hcq]; exact hd)
  rw [← hg]
  apply addOrderOf_dvd_of_nsmul_eq_zero
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective g
  rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.coe_nsmul]
  have h := (mem_killIn.1 z.2).2
  rwa [natCast_smul] at h

end KerA

/- English proof (translation)
Introduce `V _ _ B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2`. Conclude with `⟨RepsSplit_card V B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2, fun q hq hd => KerA.card_dvd_prime B Λ m₁ S₁ h1 q hq hd⟩`.
-/
theorem representatives_split : RepsSplit := by
  intro V _ _ B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2
  exact ⟨RepsSplit_card V B Λ m₁ m₂ hcop hkill SB S₁ S₂ hB h1 h2,
    fun q hq hd => KerA.card_dvd_prime B Λ m₁ S₁ h1 q hq hd⟩

end Formalism.L2.AlgTh
