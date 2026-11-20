import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveTotalOfColumns
import Development.AutomorphicArithmetic.CommutativeAlgebra.RedShDefs

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.TruncCx

open GlobalTheory.ColFilt

section Abstract

variable {A B : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]

private def ConeAt (dA : ∀ n m, A n →+ A m) (dB : ∀ n m, B n →+ B m) (Φ : ∀ n, A n →+ B n)
    (n₂ : ℤ) : Prop :=
  ∀ n₀ n₁ n₃ : ℤ, n₀ + 1 = n₁ → n₁ + 1 = n₂ → n₂ + 1 = n₃ → ∀ (x : A n₂) (y : B n₁),
    dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w

variable {GA GB : ℤ → ℤ → Type*} [∀ p n, AddCommGroup (GA p n)] [∀ p n, AddCommGroup (GB p n)]
  {dA : ∀ n m, A n →+ A m} {gA : ∀ p n m, GA p n →+ GA p m} {FA : ℤ → ∀ n, AddSubgroup (A n)}
  {rA : ∀ p n m, n + p = m → (A n →+ GA p m)}
  {dB : ∀ n m, B n →+ B m} {gB : ∀ p n m, GB p n →+ GB p m} {FB : ℤ → ∀ n, AddSubgroup (B n)}
  {rB : ∀ p n m, n + p = m → (B n →+ GB p m)}

/- English proof (translation)
Introduce `n₀ n₁ n₃ h01 h12 h23`. Take `⟨N1, hN1⟩` from `hA.bot n₂`. Take `⟨N2, hN2⟩` from `hB.bot n₁`. Establish `key : ∀ p, min (min N1 N2) 0 ≤ p → p ≤ 0 → ∀ (x : A n₂) (y : B n₁), x ∈ FA p n₂ → y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y → ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w`. Introduce `p hNp`.

Proceed by induction on `p, hNp using Int.le_induction with`. Consider the case `base`. Introduce `_ x y hxF hyF _ _`. Establish `hx0 : x = 0` using `hN1 x (hA.mono _ N1 n₂ (by omega) hxF)`. Establish `hy0 : y = 0` using `hN2 y (hB.mono _ N2 n₁ (by omega) hyF)`.

Conclude with `⟨0, 0, by simp [hx0], by simp [hy0]⟩`. Consider the case `succ q hNq ih`. Introduce `hq x y hxF hyF hx hxy`. Establish `ih'` using `ih (by omega)`. Establish `hpq : q + 1 - 1 = q` using `by ring`.

Take `⟨v₀, w₀, hv₀, hw₀⟩` from `hc (q + 1) hq (n₂ + (q + 1)) (by omega) (n₀ + (q + 1)) (n₁ + (q + 1)) (n₃ + (q + 1)) (by omega) (by omega) (by omega) (rA (q + 1) n₂ _ rfl x) (rB (q + 1) n₁ _ rfl y) (by rw [← hA.rd (q + 1) n₂ n₃ _ _ rfl rfl h23 x hxF, hx, map_zero]) (by rw [hΨ (q + 1) n₂ _ rfl x hxF, hxy, hB.rd …`. Take `⟨v, hvF, hv⟩` from `hA.surj (q + 1) n₁ _ rfl v₀`. Take `⟨w, hwF, hw⟩` from `hB.surj (q + 1) n₀ _ rfl w₀`. Establish `hx'F : x - dA n₁ n₂ v ∈ FA q n₂`. Establish `h` using `(hA.ker (q + 1) n₂ _ rfl (x - dA n₁ n₂ v) (sub_mem hxF (hA.dF (q + 1) n₁ n₂ h12 v hvF))).1 (by rw [map_sub, hA.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 v hvF, hv, hv₀, sub_self])`.

Rewrite `h` using `[hpq]`. Then use the resulting hypothesis. Establish `hy'F : y - Φ n₁ v - dB n₀ n₁ w ∈ FB q n₁`. Establish `h` using `(hB.ker (q + 1) n₁ _ rfl (y - Φ n₁ v - dB n₀ n₁ w) (sub_mem (sub_mem hyF (hF (q + 1) n₁ v hvF)) (hB.dF (q + 1) n₀ n₁ h01 w hwF))).1 (by`. Rewrite using `[map_sub, map_sub, ← hΨ (q + 1) n₁ _ rfl v hvF, hB.rd (q + 1) n₀ n₁ _ _ rfl rfl h01 w hwF, hv, hw, hw₀]`. Use the proof step `abel)`.

Rewrite `h` using `[hpq]`. Then use the resulting hypothesis. Establish `hx'c : dA n₂ n₃ (x - dA n₁ n₂ v) = 0`. Rewrite using `[map_sub, hx, hA.dd, sub_self]`. Establish `hx'r : Φ n₂ (x - dA n₁ n₂ v) = dB n₁ n₂ (y - Φ n₁ v - dB n₀ n₁ w)`. Rewrite using `[map_sub, map_sub, map_sub, hd n₁ n₂ h12 v, hxy, hB.dd, sub_zero]`.

Take `⟨v', w', hv', hw'⟩` from `ih' _ _ hx'F hy'F hx'c hx'r`. Use `⟨v + v', w + w', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ← hv']`. Normalize the expressions using the abelian group laws. Rewrite using `[map_add, map_add]`.

Rewrite `hw'` using `[sub_sub, sub_eq_iff_eq_add]`. Rewrite using `[hw']`. Normalize the expressions using the abelian group laws. Introduce `x y hx hxy`. Conclude with `key 0 (by omega) le_rfl x y (hA.top n₂ x) (hB.top n₁ y) hx hxy`.
-/
private theorem coneAt_of_graded (hA : IsFilt dA gA FA rA) (hB : IsFilt dB gB FB rB)
    (Φ : ∀ n, A n →+ B n)
    (hd : ∀ n m, n + 1 = m → ∀ x, Φ m (dA n m x) = dB n m (Φ n x))
    (hF : ∀ p n, ∀ x ∈ FA p n, Φ n x ∈ FB p n) (Ψ : ∀ p m, GA p m →+ GB p m)
    (hΨ : ∀ p n m (h : n + p = m), ∀ x ∈ FA p n, Ψ p m (rA p n m h x) = rB p n m h (Φ n x))
    (M : ℤ) (hc : ∀ p ≤ 0, ∀ k ≤ M + p, ConeAt (gA p) (gB p) (Ψ p) k)
    (n₂ : ℤ) (hn : n₂ ≤ M) : ConeAt dA dB Φ n₂ := by
  intro n₀ n₁ n₃ h01 h12 h23
  obtain ⟨N1, hN1⟩ := hA.bot n₂
  obtain ⟨N2, hN2⟩ := hB.bot n₁
  have key : ∀ p, min (min N1 N2) 0 ≤ p → p ≤ 0 → ∀ (x : A n₂) (y : B n₁), x ∈ FA p n₂ →
      y ∈ FB p n₁ → dA n₂ n₃ x = 0 → Φ n₂ x = dB n₁ n₂ y →
      ∃ (v : A n₁) (w : B n₀), x = dA n₁ n₂ v ∧ y = Φ n₁ v + dB n₀ n₁ w := by
    intro p hNp
    induction p, hNp using Int.le_induction with
    | base =>
      intro _ x y hxF hyF _ _
      have hx0 : x = 0 := hN1 x (hA.mono _ N1 n₂ (by omega) hxF)
      have hy0 : y = 0 := hN2 y (hB.mono _ N2 n₁ (by omega) hyF)
      exact ⟨0, 0, by simp [hx0], by simp [hy0]⟩
    | succ q hNq ih =>
      intro hq x y hxF hyF hx hxy
      have ih' := ih (by omega)
      have hpq : q + 1 - 1 = q := by ring
      obtain ⟨v₀, w₀, hv₀, hw₀⟩ := hc (q + 1) hq (n₂ + (q + 1)) (by omega)
        (n₀ + (q + 1)) (n₁ + (q + 1)) (n₃ + (q + 1)) (by omega) (by omega) (by omega)
        (rA (q + 1) n₂ _ rfl x) (rB (q + 1) n₁ _ rfl y)
        (by rw [← hA.rd (q + 1) n₂ n₃ _ _ rfl rfl h23 x hxF, hx, map_zero])
        (by rw [hΨ (q + 1) n₂ _ rfl x hxF, hxy, hB.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 y hyF])
      obtain ⟨v, hvF, hv⟩ := hA.surj (q + 1) n₁ _ rfl v₀
      obtain ⟨w, hwF, hw⟩ := hB.surj (q + 1) n₀ _ rfl w₀
      have hx'F : x - dA n₁ n₂ v ∈ FA q n₂ := by
        have h := (hA.ker (q + 1) n₂ _ rfl (x - dA n₁ n₂ v)
          (sub_mem hxF (hA.dF (q + 1) n₁ n₂ h12 v hvF))).1
          (by rw [map_sub, hA.rd (q + 1) n₁ n₂ _ _ rfl rfl h12 v hvF, hv, hv₀, sub_self])
        rwa [hpq] at h
      have hy'F : y - Φ n₁ v - dB n₀ n₁ w ∈ FB q n₁ := by
        have h := (hB.ker (q + 1) n₁ _ rfl (y - Φ n₁ v - dB n₀ n₁ w)
          (sub_mem (sub_mem hyF (hF (q + 1) n₁ v hvF)) (hB.dF (q + 1) n₀ n₁ h01 w hwF))).1
          (by
            rw [map_sub, map_sub, ← hΨ (q + 1) n₁ _ rfl v hvF,
              hB.rd (q + 1) n₀ n₁ _ _ rfl rfl h01 w hwF, hv, hw, hw₀]
            abel)
        rwa [hpq] at h
      have hx'c : dA n₂ n₃ (x - dA n₁ n₂ v) = 0 := by
        rw [map_sub, hx, hA.dd, sub_self]
      have hx'r : Φ n₂ (x - dA n₁ n₂ v) = dB n₁ n₂ (y - Φ n₁ v - dB n₀ n₁ w) := by
        rw [map_sub, map_sub, map_sub, hd n₁ n₂ h12 v, hxy, hB.dd, sub_zero]
      obtain ⟨v', w', hv', hw'⟩ := ih' _ _ hx'F hy'F hx'c hx'r
      refine ⟨v + v', w + w', ?_, ?_⟩
      · rw [map_add, ← hv']
        abel
      · rw [map_add, map_add]
        rw [sub_sub, sub_eq_iff_eq_add] at hw'
        rw [hw']
        abel
  intro x y hx hxy
  exact key 0 (by omega) le_rfl x y (hA.top n₂ x) (hB.top n₁ y) hx hxy

end Abstract

section Classes

variable {R : Type} [CommRing R]

private def pre {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) : Cochain L I n →+ Cochain K I n :=
  AddMonoidHom.mk' (fun α => (Cochain.ofHom g).comp α (zero_add n))
    (fun _ _ => Cochain.comp_add _ _ _ _)

/- English proof (translation)
Simplify using `[pre, Cochain.comp_zero_cochain_v]`.
-/
private theorem pre_v {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n : ℤ) (α : Cochain L I n) (t q : ℤ)
    (hq : t + n = q) : (pre g I n α).v t q hq = g.f t ≫ α.v t q hq := by
  simp [pre, Cochain.comp_zero_cochain_v]

/- English proof (translation)
Simplify using `only [pre, AddMonoidHom.mk'_apply]`. Rewrite using `[δ_ofHom_comp]`.
-/
private theorem pre_δ {K L : Cx R} (g : K ⟶ L) (I : Cx R) (n m : ℤ) (h : n + 1 = m)
    (α : Cochain L I n) : pre g I m (δ n m α) = δ n m (pre g I n α) := by
  simp only [pre, AddMonoidHom.mk'_apply]
  rw [δ_ofHom_comp]

/- English proof (translation)
Simplify using `only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]`. Use `congr 1`. Conclude with `Subtype.ext (by rw [hz]; rfl)`.
-/
private theorem cpull_mk_eq_mk_of_pre {K L I : Cx R} (g : K ⟶ L) (n : ℤ) (x : Cocycle L I n)
    (z : Cocycle K I n) (hz : (z : Cochain K I n) = pre g I n x) :
    cpull g I n (CohomologyClass.mk x) = CohomologyClass.mk z := by
  simp only [cpull, cpre, CohomologyClass.descAddMonoidHom_cohomologyClass, AddMonoidHom.mk'_apply]
  congr 1
  exact Subtype.ext (by rw [hz]; rfl)

/- English proof (translation)
Introduce `n₀ n₁ n₃ h01 h12 h23 x y hx hxy`. Simplify using `only [dC, AddMonoidHom.mk'_apply] at hx hxy ⊢`. Establish `hk1 : n₁ < M` using `by omega`. Establish `injk : Function.Injective (cpull g I k)`. Break down `lt_or_eq_of_le hk with h | h` into its components or cases.

Conclude with `(hb k h).1`. Substitute `h` using the available equality. Conclude with `hi`. Establish `hpx : δ k n₃ (pre g I k x) = 0` using `by rw [← pre_δ g I k n₃ h23, hx, map_zero]`. Establish `e1 : cpull g I k (CohomologyClass.mk (Cocycle.mk x n₃ h23 hx)) = 0`.

Rewrite using `[cpull_mk_eq_mk_of_pre g k _ (Cocycle.mk (pre g I k x) n₃ h23 hpx) rfl, ← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12]`. Conclude with `⟨y, by simp [hxy]⟩`. Establish `e2` using `injk (e1.trans (map_zero _).symm)`. Rewrite `e2` using `[← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12]`. Take `⟨v', hv'⟩` from `e2`.

Simplify using `only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hv'`. Establish `hyc : δ n₁ k (y - pre g I n₁ v') = 0`. Rewrite using `[δ_sub, ← pre_δ g I n₁ k h12, hv', hxy, sub_self]`. Take `⟨c, hc⟩` from `(hb n₁ hk1).2 (CohomologyClass.mk (Cocycle.mk _ k h12 hyc))`. Take `⟨u, rfl⟩` from `CohomologyClass.mk_surjective c`.

Establish `hpu : δ n₁ k (pre g I n₁ u) = 0`. Rewrite using `[← pre_δ g I n₁ k h12, Cocycle.δ_eq_zero, map_zero]`. Rewrite `hc` using `[cpull_mk_eq_mk_of_pre g n₁ u (Cocycle.mk (pre g I n₁ u) k h12 hpu) rfl, mk_eq_mk_iff _ _ n₀ h01]`. Take `⟨w, hw⟩` from `hc`. Simplify using `only [Cocycle.mk_coe] at hw`.

Use `⟨v' + u, -w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[δ_add, hv', Cocycle.δ_eq_zero, add_zero]`. Rewrite using `[map_add, δ_neg, hw]`. Normalize the expressions using the abelian group laws.
-/
private theorem coneAt_of_conn {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (hb : ∀ n, n < M → Function.Bijective (cpull g I n)) (hi : Function.Injective (cpull g I M))
    (k : ℤ) (hk : k ≤ M) : ConeAt (dC L I) (dC K I) (pre g I) k := by
  intro n₀ n₁ n₃ h01 h12 h23 x y hx hxy
  simp only [dC, AddMonoidHom.mk'_apply] at hx hxy ⊢
  have hk1 : n₁ < M := by omega
  have injk : Function.Injective (cpull g I k) := by
    rcases lt_or_eq_of_le hk with h | h
    · exact (hb k h).1
    · subst h
      exact hi
  have hpx : δ k n₃ (pre g I k x) = 0 := by rw [← pre_δ g I k n₃ h23, hx, map_zero]
  have e1 : cpull g I k (CohomologyClass.mk (Cocycle.mk x n₃ h23 hx)) = 0 := by
    rw [cpull_mk_eq_mk_of_pre g k _ (Cocycle.mk (pre g I k x) n₃ h23 hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ n₁ h12]
    exact ⟨y, by simp [hxy]⟩
  have e2 := injk (e1.trans (map_zero _).symm)
  rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ n₁ h12] at e2
  obtain ⟨v', hv'⟩ := e2
  simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hv'
  have hyc : δ n₁ k (y - pre g I n₁ v') = 0 := by
    rw [δ_sub, ← pre_δ g I n₁ k h12, hv', hxy, sub_self]
  obtain ⟨c, hc⟩ := (hb n₁ hk1).2 (CohomologyClass.mk (Cocycle.mk _ k h12 hyc))
  obtain ⟨u, rfl⟩ := CohomologyClass.mk_surjective c
  have hpu : δ n₁ k (pre g I n₁ u) = 0 := by
    rw [← pre_δ g I n₁ k h12, Cocycle.δ_eq_zero, map_zero]
  rw [cpull_mk_eq_mk_of_pre g n₁ u (Cocycle.mk (pre g I n₁ u) k h12 hpu) rfl, mk_eq_mk_iff _ _ n₀ h01] at hc
  obtain ⟨w, hw⟩ := hc
  simp only [Cocycle.mk_coe] at hw
  refine ⟨v' + u, -w, ?_, ?_⟩
  · rw [δ_add, hv', Cocycle.δ_eq_zero, add_zero]
  · rw [map_add, δ_neg, hw]
    abel

/- English proof (translation)
Establish `inj : ∀ n, n ≤ M → Function.Injective (cpull g I n)`. Introduce `n hn`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨x, rfl⟩` from `CohomologyClass.mk_surjective c`.

Establish `hpx : δ n (n + 1) (pre g I n x) = 0`. Rewrite using `[← pre_δ g I n (n + 1) rfl, Cocycle.δ_eq_zero, map_zero]`. Rewrite `hc` using `[cpull_mk_eq_mk_of_pre g n x (Cocycle.mk _ (n + 1) rfl hpx) rfl, ← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]`. Take `⟨y, hy⟩` from `hc`. Simplify using `only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hy`.

Take `⟨v, w, hv, -⟩` from `h n hn (n - 1 - 1) (n - 1) (n + 1) (by ring) (by ring) rfl (x : Cochain L I n) y (Cocycle.δ_eq_zero x _) (by simp only [dC, AddMonoidHom.mk'_apply, hy])`. Rewrite using `[← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]`. Simplify using `only [dC, AddMonoidHom.mk'_apply] at hv`. Conclude with `⟨v, by rw [← hv]; simp⟩`. Use `⟨fun n hn => ⟨inj n hn.le, ?_⟩, inj M le_rfl⟩` and prove the remaining obligations.

Introduce `c`. Take `⟨z, rfl⟩` from `CohomologyClass.mk_surjective c`. Take `⟨v, w, hv, hw⟩` from `h (n + 1) (by omega) (n - 1) n (n + 1 + 1) (by ring) rfl rfl 0 (z : Cochain K I n) (map_zero _) (by simp [dC, Cocycle.δ_eq_zero])`. Simplify using `only [dC, AddMonoidHom.mk'_apply] at hv hw`. Establish `hvδ : δ n (n + 1) v = 0` using `hv.symm`.

Establish `hpv : δ n (n + 1) (pre g I n v) = 0`. Rewrite using `[← pre_δ g I n (n + 1) rfl, hvδ, map_zero]`. Use `⟨CohomologyClass.mk (Cocycle.mk v (n + 1) rfl hvδ), ?_⟩` and prove the remaining obligations. Rewrite using `[cpull_mk_eq_mk_of_pre g n _ (Cocycle.mk (pre g I n v) (n + 1) rfl hpv) rfl, mk_eq_mk_iff _ _ (n - 1) (by ring)]`. Use `⟨-w, ?_⟩` and prove the remaining obligations.

Simplify using `only [Cocycle.mk_coe, δ_neg, hw]`. Normalize the expressions using the abelian group laws.
-/
private theorem conn_of_coneAt {K L I : Cx R} (g : K ⟶ L) (M : ℤ)
    (h : ∀ k ≤ M, ConeAt (dC L I) (dC K I) (pre g I) k) :
    (∀ n, n < M → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I M) := by
  have inj : ∀ n, n ≤ M → Function.Injective (cpull g I n) := by
    intro n hn
    rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective c
    have hpx : δ n (n + 1) (pre g I n x) = 0 := by
      rw [← pre_δ g I n (n + 1) rfl, Cocycle.δ_eq_zero, map_zero]
    rw [cpull_mk_eq_mk_of_pre g n x (Cocycle.mk _ (n + 1) rfl hpx) rfl, ← CohomologyClass.mk_zero,
      mk_eq_mk_iff _ _ (n - 1) (by ring)] at hc
    obtain ⟨y, hy⟩ := hc
    simp only [Cocycle.mk_coe, Cocycle.coe_zero, sub_zero] at hy
    obtain ⟨v, w, hv, -⟩ := h n hn (n - 1 - 1) (n - 1) (n + 1) (by ring) (by ring) rfl
      (x : Cochain L I n) y (Cocycle.δ_eq_zero x _) (by simp only [dC, AddMonoidHom.mk'_apply, hy])
    rw [← CohomologyClass.mk_zero, mk_eq_mk_iff _ _ (n - 1) (by ring)]
    simp only [dC, AddMonoidHom.mk'_apply] at hv
    exact ⟨v, by rw [← hv]; simp⟩
  refine ⟨fun n hn => ⟨inj n hn.le, ?_⟩, inj M le_rfl⟩
  intro c
  obtain ⟨z, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨v, w, hv, hw⟩ := h (n + 1) (by omega) (n - 1) n (n + 1 + 1) (by ring) rfl rfl 0
    (z : Cochain K I n) (map_zero _) (by simp [dC, Cocycle.δ_eq_zero])
  simp only [dC, AddMonoidHom.mk'_apply] at hv hw
  have hvδ : δ n (n + 1) v = 0 := hv.symm
  have hpv : δ n (n + 1) (pre g I n v) = 0 := by
    rw [← pre_δ g I n (n + 1) rfl, hvδ, map_zero]
  refine ⟨CohomologyClass.mk (Cocycle.mk v (n + 1) rfl hvδ), ?_⟩
  rw [cpull_mk_eq_mk_of_pre g n _ (Cocycle.mk (pre g I n v) (n + 1) rfl hpv) rfl,
    mk_eq_mk_iff _ _ (n - 1) (by ring)]
  refine ⟨-w, ?_⟩
  simp only [Cocycle.mk_coe, δ_neg, hw]
  abel

end Classes

end UpperTheory.TruncCx

/- English proof (translation)
Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Establish `hct : t = c` using `by omega`. Substitute `hct` using the available equality. Rewrite using `[GlobalTheory.ColFilt.ιTerm_zero, GlobalTheory.ColFilt.ιTerm_zero]`.

Simplify using `[CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self]`. Rewrite using `[GlobalTheory.ColFilt.ιTerm_ne K c k t h hk, GlobalTheory.ColFilt.ιTerm_ne L c k t h hk]`. Simplify using the standard rewrite rules.
-/
private theorem ιTerm_comp_f_naturality {R : Type} [CommRing R] {K L : Cx R} (g : K ⟶ L) (c k t : ℤ)
    (h : c + k = t) :
    GlobalTheory.ColFilt.ιTerm K c k t h ≫ g.f t =
      ((CochainComplex.singleFunctor (Shv R) 0).map (g.f c)).f k ≫ GlobalTheory.ColFilt.ιTerm L c k t h := by
  by_cases hk : k = 0
  · subst hk
    have hct : t = c := by omega
    subst hct
    rw [GlobalTheory.ColFilt.ιTerm_zero, GlobalTheory.ColFilt.ιTerm_zero]
    simp [CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self]
  · rw [GlobalTheory.ColFilt.ιTerm_ne K c k t h hk, GlobalTheory.ColFilt.ιTerm_ne L c k t h hk]
    simp

open GlobalTheory.ColFilt UpperTheory.TruncCx in
/- English proof (translation)
Introduce `R _ I _ _ K L _ _ g m hyp`. Apply `UpperTheory.TruncCx.conn_of_coneAt g m` to reduce the goal to its premises. Introduce `k hk`. Use `UpperTheory.TruncCx.coneAt_of_graded ((isColumns_terms L).isFilt I) ((isColumns_terms K).isFilt I) (UpperTheory.TruncCx.pre g I) (fun n m' h x => UpperTheory.TruncCx.pre_δ g I n m' h x) ?_ (fun p => UpperTheory.TruncCx.pre ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I) …` and prove the remaining obligations. Introduce `p n x hx c k' t h q hq hpc`.

Establish `hx' : ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c → ιTerm L c k t h ≫ x.v t q hq = 0` using `hx`. Rewrite using `[UpperTheory.TruncCx.pre_v, ← Category.assoc, ιTerm_comp_f_naturality, Category.assoc, hx' c k' t h q hq hpc, comp_zero]`. Introduce `p n m' h x _`. Use `Cochain.ext _ _ (fun k' q hq => ?_)` and prove the remaining obligations. Rewrite using `[UpperTheory.TruncCx.pre_v, restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), UpperTheory.TruncCx.pre_v, ← Category.assoc, ← Category.assoc, ιTerm_comp_f_naturality]`.
-/
theorem UpperTheory.cochainPullback_bijective_of_termwise_bijective_injective :
    ∀ (R : Type) [CommRing R] (I : Cx R) [I.IsStrictlyGE 0], (∀ n, Injective (I.X n)) → ∀ {K L : Cx R} [K.IsStrictlyLE 0] [L.IsStrictlyLE 0] (g : K ⟶ L) (m : ℤ), (∀ p : ℤ, (∀ n, n < m + p → Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I n)) ∧ Function.Injective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I (m + p))) → (∀ n, n < m → Function.Bijective (cpull g I n)) ∧ Function.Injective (cpull g I m) := by
  intro R _ I _ _ K L _ _ g m hyp
  apply UpperTheory.TruncCx.conn_of_coneAt g m
  intro k hk
  refine UpperTheory.TruncCx.coneAt_of_graded ((isColumns_terms L).isFilt I) ((isColumns_terms K).isFilt I)
    (UpperTheory.TruncCx.pre g I) (fun n m' h x => UpperTheory.TruncCx.pre_δ g I n m' h x) ?_
    (fun p => UpperTheory.TruncCx.pre ((CochainComplex.singleFunctor (Shv R) 0).map (g.f p)) I) ?_ m
    (fun p _ k' hk' => UpperTheory.TruncCx.coneAt_of_conn _ (m + p) (hyp p).1 (hyp p).2 k' hk') k hk
  · intro p n x hx c k' t h q hq hpc
    have hx' : ∀ (c k t : ℤ) (h : c + k = t) (q : ℤ) (hq : t + n = q), p < c →
        ιTerm L c k t h ≫ x.v t q hq = 0 := hx
    rw [UpperTheory.TruncCx.pre_v, ← Category.assoc, ιTerm_comp_f_naturality, Category.assoc,
      hx' c k' t h q hq hpc, comp_zero]
  · intro p n m' h x _
    refine Cochain.ext _ _ (fun k' q hq => ?_)
    rw [UpperTheory.TruncCx.pre_v, restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega),
      restr_v _ _ p n m' h _ k' (p + k') q rfl hq (by omega), UpperTheory.TruncCx.pre_v,
      ← Category.assoc, ← Category.assoc, ιTerm_comp_f_naturality]
