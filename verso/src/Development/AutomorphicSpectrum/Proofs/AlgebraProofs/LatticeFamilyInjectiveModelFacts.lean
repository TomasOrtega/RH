import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsLatticeFamily
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeFiniteProjectiveBaseChange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AffineGenerators
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg restrictChart fnField ck rootNum SameGeneric LatLE IsPull IsPullBC)

namespace GlobalTheory.CompanionTheory.Ar.Num.FamConstr

section Closure

variable (o : Type) [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
variable {x : (Σ k, ι k) → Ω}

variable {o} in

/- English proof (translation)
Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hm`. Use `h.1 t ht _ (pow_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t s) k) _ hv` as an intermediate fact. Rewrite `this` using `[smul_smul, ← pow_add, add_comm]`. Then use the resulting hypothesis.
-/
theorem up {Γ : (∀ k, ι k) → AddSubgroup V} (h : IsLatFamily o x Γ) {s t : ∀ k, ι k} (ht : mseg x t ≠ 0)
    {v : V} {m m' : ℕ} (hm : m ≤ m') (hv : (mseg x s / mseg x t) ^ m • v ∈ Γ t) :
    (mseg x s / mseg x t) ^ m' • v ∈ Γ t := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have := h.1 t ht _ (pow_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t s) k) _ hv
  rwa [smul_smul, ← pow_add, add_comm] at this

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Take `⟨y, hy, z, hz, rfl⟩` from `AddSubgroup.mem_sup.1 hv`. Rewrite using `[smul_add]`. Conclude with `add_mem (AddSubgroup.mem_sup_left (hA.1 c hc a ha y hy)) (AddSubgroup.mem_sup_right (hB.1 c hc a ha z hz))`. Take `⟨y, hy, z, hz, rfl⟩` from `AddSubgroup.mem_sup.1 hv`.

Take `⟨m₁, h₁⟩` from `hA.2 c t hc ht y hy`. Take `⟨m₂, h₂⟩` from `hB.2 c t hc ht z hz`. Use `⟨m₁ + m₂, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Conclude with `add_mem (AddSubgroup.mem_sup_left (up hA ht (Nat.le_add_right _ _) h₁)) (AddSubgroup.mem_sup_right (up hB ht (Nat.le_add_left _ _) h₂))`.
-/
theorem sup {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x fun c => A c ⊔ B c := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    rw [smul_add]
    exact add_mem (AddSubgroup.mem_sup_left (hA.1 c hc a ha y hy))
      (AddSubgroup.mem_sup_right (hB.1 c hc a ha z hz))
  · obtain ⟨y, hy, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    obtain ⟨m₁, h₁⟩ := hA.2 c t hc ht y hy
    obtain ⟨m₂, h₂⟩ := hB.2 c t hc ht z hz
    refine ⟨m₁ + m₂, ?_⟩
    rw [smul_add]
    exact add_mem (AddSubgroup.mem_sup_left (up hA ht (Nat.le_add_right _ _) h₁))
      (AddSubgroup.mem_sup_right (up hB ht (Nat.le_add_left _ _) h₂))

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ⟨hA.1 c hc a ha v hv.1, hB.1 c hc a ha v hv.2⟩, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Take `⟨m₁, h₁⟩` from `hA.2 c t hc ht v hv.1`. Take `⟨m₂, h₂⟩` from `hB.2 c t hc ht v hv.2`. Conclude with `⟨m₁ + m₂, up hA ht (Nat.le_add_right _ _) h₁, up hB ht (Nat.le_add_left _ _) h₂⟩`.
-/
theorem inf {A B : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x fun c => A c ⊓ B c := by
  refine ⟨fun c hc a ha v hv => ⟨hA.1 c hc a ha v hv.1, hB.1 c hc a ha v hv.2⟩,
    fun c t hc ht v hv => ?_⟩
  obtain ⟨m₁, h₁⟩ := hA.2 c t hc ht v hv.1
  obtain ⟨m₂, h₂⟩ := hB.2 c t hc ht v hv.2
  exact ⟨m₁ + m₂, up hA ht (Nat.le_add_right _ _) h₁, up hB ht (Nat.le_add_left _ _) h₂⟩

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Establish `h` using `AddSubgroup.mem_prod.1 hv`. Conclude with `AddSubgroup.mem_prod.2 ⟨hA.1 c hc a ha _ h.1, hB.1 c hc a ha _ h.2⟩`. Establish `h` using `AddSubgroup.mem_prod.1 hv`. Take `⟨m₁, h₁⟩` from `hA.2 c t hc ht _ h.1`.

Take `⟨m₂, h₂⟩` from `hB.2 c t hc ht _ h.2`. Conclude with `⟨m₁ + m₂, AddSubgroup.mem_prod.2 ⟨up hA ht (Nat.le_add_right _ _) h₁, up hB ht (Nat.le_add_left _ _) h₂⟩⟩`.
-/
theorem prod {A : (∀ k, ι k) → AddSubgroup V} {B : (∀ k, ι k) → AddSubgroup V₁}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B) :
    IsLatFamily o x fun c => (A c).prod (B c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · have h := AddSubgroup.mem_prod.1 hv
    exact AddSubgroup.mem_prod.2 ⟨hA.1 c hc a ha _ h.1, hB.1 c hc a ha _ h.2⟩
  · have h := AddSubgroup.mem_prod.1 hv
    obtain ⟨m₁, h₁⟩ := hA.2 c t hc ht _ h.1
    obtain ⟨m₂, h₂⟩ := hB.2 c t hc ht _ h.2
    exact ⟨m₁ + m₂, AddSubgroup.mem_prod.2 ⟨up hA ht (Nat.le_add_right _ _) h₁,
      up hB ht (Nat.le_add_left _ _) h₂⟩⟩

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[AddSubgroup.mem_comap, hg]`. Conclude with `hA.1 c hc a ha _ hv`. Take `⟨m, hm⟩` from `hA.2 c t hc ht _ hv`. Conclude with `⟨m, by rw [AddSubgroup.mem_comap, hg]; exact hm⟩`.
-/
theorem comap (g : V →+ V₁) (hg : ∀ (a : Ω) (v : V), g (a • v) = a • g v)
    {A : (∀ k, ι k) → AddSubgroup V₁} (hA : IsLatFamily o x A) :
    IsLatFamily o x fun c => (A c).comap g := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · rw [AddSubgroup.mem_comap, hg]
    exact hA.1 c hc a ha _ hv
  · obtain ⟨m, hm⟩ := hA.2 c t hc ht _ hv
    exact ⟨m, by rw [AddSubgroup.mem_comap, hg]; exact hm⟩

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Take `⟨u, hu, rfl⟩` from `AddSubgroup.mem_map.1 hv`. Conclude with `AddSubgroup.mem_map.2 ⟨a • u, hA.1 c hc a ha u hu, hg a u⟩`. Take `⟨u, hu, rfl⟩` from `AddSubgroup.mem_map.1 hv`. Take `⟨m, hm⟩` from `hA.2 c t hc ht u hu`.

Conclude with `⟨m, AddSubgroup.mem_map.2 ⟨_, hm, hg _ u⟩⟩`.
-/
theorem map (g : V →+ V₁) (hg : ∀ (a : Ω) (v : V), g (a • v) = a • g v)
    {A : (∀ k, ι k) → AddSubgroup V} (hA : IsLatFamily o x A) :
    IsLatFamily o x fun c => (A c).map g := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hv
    exact AddSubgroup.mem_map.2 ⟨a • u, hA.1 c hc a ha u hu, hg a u⟩
  · obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.1 hv
    obtain ⟨m, hm⟩ := hA.2 c t hc ht u hu
    exact ⟨m, AddSubgroup.mem_map.2 ⟨_, hm, hg _ u⟩⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ _ a _ v hv => hG a v hv, fun _ _ _ _ v hv => ⟨0, by simpa using hv⟩⟩`.
-/
theorem const (G : AddSubgroup V) (hG : ∀ (a : Ω), ∀ v ∈ G, a • v ∈ G) :
    IsLatFamily o x fun _ => G :=
  ⟨fun _ _ a _ v hv => hG a v hv, fun _ _ _ _ v hv => ⟨0, by simpa using hv⟩⟩

/- English proof (translation)
The claim follows from `const o _ fun _ _ _ => AddSubgroup.mem_top _`.
-/
theorem top : IsLatFamily o x fun _ => (⊤ : AddSubgroup V) :=
  const o _ fun _ _ _ => AddSubgroup.mem_top _

/- English proof (translation)
The claim follows from `const o _ fun a v hv => by rw [AddSubgroup.mem_bot] at hv ⊢ rw [hv, smul_zero]`.
-/
theorem bot : IsLatFamily o x fun _ => (⊥ : AddSubgroup V) :=
  const o _ fun a v hv => by
    rw [AddSubgroup.mem_bot] at hv ⊢
    rw [hv, smul_zero]

/- English proof (translation)
The claim follows from `const o _ fun a _ hv => U.smul_mem a hv`.
-/
theorem sub (U : Submodule Ω V) : IsLatFamily o x fun _ => U.toAddSubgroup :=
  const o _ fun a _ hv => U.smul_mem a hv

/- English proof (translation)
Simplify using `[stdLat, AddSubgroup.mem_pi]`.
-/
theorem mem_std (R : Subalgebra o Ω) {κ : Type} (v : κ → Ω) :
    v ∈ stdLat R κ ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Conclude with `(mem_std o _ _).2 fun i => by simpa using mul_mem ha ((mem_std o _ _).1 hv i)`. Use `choose m hm using fun i => ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing (o := o) (mseg x) c t hc ((mem_std o _ _).1 hv i)`. Use `⟨∑ i, m i, (mem_std o _ _).2 fun i => ?_⟩` and prove the remaining obligations. Establish `hle : m i ≤ ∑ i, m i` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`.

Rewrite using `[← Nat.sub_add_cancel hle, pow_add, Pi.smul_apply, smul_eq_mul, mul_assoc]`. Conclude with `mul_mem (pow_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c) _) (hm i)`.
-/
theorem std (κ : Type) [Fintype κ] : IsLatFamily o x fun c => stdLat (chartRing o (mseg x) c) κ := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · exact (mem_std o _ _).2 fun i => by simpa using mul_mem ha ((mem_std o _ _).1 hv i)
  · choose m hm using fun i =>
      ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing (o := o) (mseg x) c t hc ((mem_std o _ _).1 hv i)
    refine ⟨∑ i, m i, (mem_std o _ _).2 fun i => ?_⟩
    have hle : m i ≤ ∑ i, m i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [← Nat.sub_add_cancel hle, pow_add, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact mul_mem (pow_mem (ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c) _) (hm i)

/- English proof (translation)
Simplify using `[dotDual, AddSubgroup.mem_iInf]`.
-/
theorem mem_dual (R : Subalgebra o Ω) {m : ℕ} (L : AddSubgroup (Fin m → Ω)) (v : Fin m → Ω) :
    v ∈ dotDual R L ↔ ∀ l ∈ L, l ⬝ᵥ v ∈ R := by
  simp [dotDual, AddSubgroup.mem_iInf]

/- English proof (translation)
Use `⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩` and prove the remaining obligations. Use `(mem_dual o _ _ _).2 fun l hl => ?_` and prove the remaining obligations. Rewrite using `[dotProduct_smul, smul_eq_mul]`. Conclude with `mul_mem ha ((mem_dual o _ _ _).1 hv l hl)`. Take `⟨S, hS, hspan⟩` from `hfg t ht`.

Establish `hu : mseg x c / mseg x t ∈ chartRing o (mseg x) t` using `ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c`. Establish `key : ∀ g ∈ S, ∃ k : ℕ, (mseg x c / mseg x t) ^ k * (g ⬝ᵥ v) ∈ chartRing o (mseg x) t`. Introduce `g hg`. Take `⟨m', hm'⟩` from `hL.2 t c ht hc g (hS hg)`. Establish `h1` using `(mem_dual o _ _ _).1 hv _ hm'`.

Rewrite `h1` using `[smul_dotProduct, smul_eq_mul]`. Take `⟨k, hk⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing (o := o) (mseg x) c t hc h1`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `h2` using `mul_mem (pow_mem hu m') hk`. Establish `e1 : (mseg x c / mseg x t) ^ m' * (mseg x t / mseg x c) ^ m' = 1`.

Rewrite using `[← mul_pow, div_mul_div_comm, mul_comm (mseg x c), div_self (mul_ne_zero ht hc), one_pow]`. Establish `e : (mseg x c / mseg x t) ^ m' * ((mseg x c / mseg x t) ^ k * ((mseg x t / mseg x c) ^ m' * (g ⬝ᵥ v))) = (mseg x c / mseg x t) ^ k * (g ⬝ᵥ v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Use `choose! k hk using key`.

Establish `hall : ∀ l' ∈ spanOver (chartRing o (mseg x) t) (S : Set (Fin m → Ω)), l' ⬝ᵥ ((mseg x c / mseg x t) ^ (∑ g ∈ S, k g) • v) ∈ chartRing o (mseg x) t`. Introduce `l' hl'`. Unfold `spanOver at hl'`. Proceed by induction on `hl' using AddSubgroup.closure_induction with`. Consider the case `mem y hy`.

Take `⟨a, ha, e, he, rfl⟩` from `hy`. Rewrite using `[smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]`. Use `mul_mem ha ?_` and prove the remaining obligations. Establish `hle : k e ≤ ∑ g ∈ S, k g` using `Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) he`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc]`.

Conclude with `mul_mem (pow_mem hu _) (hk e he)`. Consider the case `zero`. Rewrite using `[zero_dotProduct]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb`.

Rewrite using `[add_dotProduct]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha`. Rewrite using `[neg_dotProduct]`. Conclude with `neg_mem ha`.

Conclude with `⟨∑ g ∈ S, k g, (mem_dual o _ _ _).2 fun l hl => hall l (hspan hl)⟩`.
-/
theorem dual {m : ℕ} {L : (∀ k, ι k) → AddSubgroup (Fin m → Ω)} (hL : IsLatFamily o x L)
    (hfg : ∀ c, mseg x c ≠ 0 → ∃ S : Finset (Fin m → Ω), (S : Set (Fin m → Ω)) ⊆ L c ∧
      L c ≤ spanOver (chartRing o (mseg x) c) (S : Set (Fin m → Ω))) :
    IsLatFamily o x fun c => dotDual (chartRing o (mseg x) c) (L c) := by
  refine ⟨fun c hc a ha v hv => ?_, fun c t hc ht v hv => ?_⟩
  · refine (mem_dual o _ _ _).2 fun l hl => ?_
    rw [dotProduct_smul, smul_eq_mul]
    exact mul_mem ha ((mem_dual o _ _ _).1 hv l hl)
  · obtain ⟨S, hS, hspan⟩ := hfg t ht
    have hu : mseg x c / mseg x t ∈ chartRing o (mseg x) t :=
      ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (o := o) (mseg x) t c
    have key : ∀ g ∈ S, ∃ k : ℕ, (mseg x c / mseg x t) ^ k * (g ⬝ᵥ v) ∈ chartRing o (mseg x) t := by
      intro g hg
      obtain ⟨m', hm'⟩ := hL.2 t c ht hc g (hS hg)
      have h1 := (mem_dual o _ _ _).1 hv _ hm'
      rw [smul_dotProduct, smul_eq_mul] at h1
      obtain ⟨k, hk⟩ := ReciprocityTheory.ChartRestriction.G.Geo.exists_pow_mul_mem_chartRing (o := o) (mseg x) c t hc h1
      refine ⟨k, ?_⟩
      have h2 := mul_mem (pow_mem hu m') hk
      have e1 : (mseg x c / mseg x t) ^ m' * (mseg x t / mseg x c) ^ m' = 1 := by
        rw [← mul_pow, div_mul_div_comm, mul_comm (mseg x c), div_self (mul_ne_zero ht hc), one_pow]
      have e : (mseg x c / mseg x t) ^ m' * ((mseg x c / mseg x t) ^ k *
          ((mseg x t / mseg x c) ^ m' * (g ⬝ᵥ v))) = (mseg x c / mseg x t) ^ k * (g ⬝ᵥ v) := by
        calc _ = ((mseg x c / mseg x t) ^ m' * (mseg x t / mseg x c) ^ m') *
              ((mseg x c / mseg x t) ^ k * (g ⬝ᵥ v)) := by ring
          _ = _ := by rw [e1, one_mul]
      rwa [e] at h2
    choose! k hk using key
    have hall : ∀ l' ∈ spanOver (chartRing o (mseg x) t) (S : Set (Fin m → Ω)),
        l' ⬝ᵥ ((mseg x c / mseg x t) ^ (∑ g ∈ S, k g) • v) ∈ chartRing o (mseg x) t := by
      intro l' hl'
      unfold spanOver at hl'
      induction hl' using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨a, ha, e, he, rfl⟩ := hy
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        refine mul_mem ha ?_
        have hle : k e ≤ ∑ g ∈ S, k g := Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) he
        rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
        exact mul_mem (pow_mem hu _) (hk e he)
      | zero =>
        rw [zero_dotProduct]
        exact zero_mem _
      | add a b _ _ ha hb =>
        rw [add_dotProduct]
        exact add_mem ha hb
      | neg a _ ha =>
        rw [neg_dotProduct]
        exact neg_mem ha
    exact ⟨∑ g ∈ S, k g, (mem_dual o _ _ _).2 fun l hl => hall l (hspan hl)⟩

end Closure

section Gens

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type} [AddCommGroup E] [Module Ω E]

/- English proof (translation)
Unfold `spanOver at hv ⊢`. Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, e, he, rfl⟩` from `hy`. Conclude with `AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, e, he, by rw [smul_smul]⟩`.

Consider the case `zero`. Rewrite using `[smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Rewrite using `[smul_add]`.

Conclude with `add_mem hy hz`. Consider the case `neg y _ hy`. Rewrite using `[smul_neg]`. Conclude with `neg_mem hy`.
-/
theorem smul_mem_span (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {v : E}
    (hv : v ∈ spanOver R S) : a • v ∈ spanOver R S := by
  unfold spanOver at hv ⊢
  induction hv using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, e, he, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨a * b, mul_mem ha hb, e, he, by rw [smul_smul]⟩
  | zero =>
    rw [smul_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    rw [smul_add]
    exact add_mem hy hz
  | neg y _ hy =>
    rw [smul_neg]
    exact neg_mem hy

/- English proof (translation)
Set `N : Submodule R E` to `{ toAddSubmonoid := L.toAddSubmonoid smul_mem' := fun a e he => h.1 a a.2 e he }`. Establish `hN : N.toAddSubgroup = L`. Use extensionality with `e`. Both sides reduce to the same expression. Establish `hfin : Module.Finite R N` using `(GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main R r N (by rw [hN]; exact h)).1`.

Take `⟨S, hS⟩` from `(Module.Finite.iff_fg).1 hfin`. Use `⟨S, fun e he => ?_, fun e he => ?_⟩` and prove the remaining obligations. Establish `: e ∈ N` using `hS ▸ Submodule.subset_span he`. Conclude with `this`. Establish `hall : ∀ y ∈ Submodule.span R (S : Set E), y ∈ spanOver R (S : Set E)`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact AddSubgroup.subset_closure ⟨1, one_mem _, y, hy, by simp⟩`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`.

Consider the case `smul a b _ hb => exact smul_mem_span R _ a.2 hb`. Conclude with `hall e (by rw [hS]; exact he)`.
-/
theorem exists_gens (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E) (h : LocFree R r L) :
    ∃ S : Finset E, (S : Set E) ⊆ L ∧ L ≤ spanOver R (S : Set E) := by
  let N : Submodule R E :=
    { toAddSubmonoid := L.toAddSubmonoid
      smul_mem' := fun a e he => h.1 a a.2 e he }
  have hN : N.toAddSubgroup = L := by
    ext e
    rfl
  have hfin : Module.Finite R N := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj.main R r N (by rw [hN]; exact h)).1
  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg).1 hfin
  refine ⟨S, fun e he => ?_, fun e he => ?_⟩
  · have : e ∈ N := hS ▸ Submodule.subset_span he
    exact this
  · have hall : ∀ y ∈ Submodule.span R (S : Set E), y ∈ spanOver R (S : Set E) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact AddSubgroup.subset_closure ⟨1, one_mem _, y, hy, by simp⟩
      | zero => exact zero_mem _
      | add a b _ _ ha hb => exact add_mem ha hb
      | smul a b _ hb => exact smul_mem_span R _ a.2 hb
    exact hall e (by rw [hS]; exact he)

variable {F : Type} [Zero F] [One F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ}

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.AffineGenerators.af_gens D R p N χ h0 h1 hl hs`.
-/
theorem af_gens (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p N : ℕ) (χ : F → Ω) (h0 : χ 0 = 0)
    (h1 : χ 1 = 1) (hl : LocFree R N (D.l1 R p))
    (hs : Summand (D.l1 R p) (LinearMap.range (linMap n χ))) :
    ∃ S : Finset (Fin n → Ω), (S : Set (Fin n → Ω)) ⊆ D.af R p χ ∧
      D.af R p χ ≤ spanOver R (S : Set (Fin n → Ω)) :=
  _root_.UpperTheory.Reformulated.B.AffineGenerators.af_gens D R p N χ h0 h1 hl hs

end Gens

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D h`. Establish `hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p)`. Use `sup O h.famM (map O (DistribMulAction.toAddMonoidHom ((Fin n → F) → Ω) (p : Ω)) (fun a v => smul_comm _ _ _) (std O (x := x) (Fin n → F)))` as an intermediate fact. Conclude with `this`. Establish `haf : ∀ χ' : F → Ω, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p χ')`.

Introduce `χ'`. Use `comap O (linMap n χ').toAddMonoidHom (fun a v => map_smul (linMap n χ') a v) hl1` as an intermediate fact. Conclude with `this`. Use `⟨hl1, fun τ => ⟨haf _, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hg => ?_⟩⟩` and prove the remaining obligations. Use `comap O (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))).toAddMonoidHom (fun a v => map_smul (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))) a v) (sup O h.famM (sub O (vanSub Ω F n ((i : ℕ) + 1))))` as an intermediate fact.

Conclude with `this`. Use `comap O ((LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))).toAddMonoidHom.prodMap (AddMonoidHom.id (Fin (r τ) → Ω))) (fun a v => Prod.ext (map_smul (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))) a v.1) rfl) (s …` as an intermediate fact. Conclude with `this`. Use `map O (AddMonoidHom.snd ((Fin n → F) → Ω) (Fin (r τ) → Ω)) (fun a v => rfl) (inf O (h.fam τ).2.2.2.2.2.2 (prod O (sub O (vanSub Ω F n i)) (top O)))` as an intermediate fact. Conclude with `this`.

Conclude with `dual O (h.fam τ).1 fun c hc => exists_gens _ _ _ ((h.base c hc).free τ).1`. Establish `h01` using `(h.char.2.2.2.2 τ)`. Establish `hh : IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a)))` using `dual O (haf _) fun c hc => af_gens (D c) _ p _ _ (by simp [h01.1]) (by simp [h01.2]) (hg c hc).l1 ((hg c hc).lin τ)`. Use `⟨hh, ?_⟩` and prove the remaining obligations. Use `map O (AddMonoidHom.snd (Fin n → Ω) (Fin (s τ) → Ω)) (fun a v => rfl) (inf O (h.fam τ).2.2.2.2.2.1 (prod O hh (top O)))` as an intermediate fact.

Conclude with `this`.
-/
theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω), Function.Injective (algebraMap O Ω) → ∀ {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} [Fintype Sg] {r s : Sg → ℕ} (p : ℕ), p.Prime → ∀ (w : O) (χ : Sg → F → O) (φ : Equiv.Perm Sg) (D : (∀ k, ι k) → LieLatticeData Ω F n Sg r s), IsLatticeFamily O x p w χ φ D → IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) ∧ ∀ τ, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ (∀ i, IsLatFamily O x (fun c => (D c).xId (fun a => algebraMap O Ω (χ τ a)) i) ∧ IsLatFamily O x (fun c => (D c).stepGraph τ (fun a => algebraMap O Ω (χ τ a)) i)) ∧ (∀ i, IsLatFamily O x (fun c => (D c).kk τ i)) ∧ IsLatFamily O x (fun c => dotDual (chartRing O (mseg x) c) ((D c).lie τ)) ∧ ((∀ c, mseg x c ≠ 0 → (D c).Good₁ (chartRing O (mseg x) c) p (fun τ a => algebraMap O Ω (χ τ a))) → IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p (fun a => algebraMap O Ω (χ τ a))) ∧ IsLatFamily O x (fun c => (D c).imH (chartRing O (mseg x) c) p τ (fun a => algebraMap O Ω (χ τ a)))) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x _ F _ _ _ n Sg _ r s p _ w χ φ D h
  have hl1 : IsLatFamily O x (fun c => (D c).l1 (chartRing O (mseg x) c) p) := by
    have := sup O h.famM (map O (DistribMulAction.toAddMonoidHom ((Fin n → F) → Ω) (p : Ω))
      (fun a v => smul_comm _ _ _) (std O (x := x) (Fin n → F)))
    exact this
  have haf : ∀ χ' : F → Ω, IsLatFamily O x (fun c => (D c).af (chartRing O (mseg x) c) p χ') := by
    intro χ'
    have := comap O (linMap n χ').toAddMonoidHom (fun a v => map_smul (linMap n χ') a v) hl1
    exact this
  refine ⟨hl1, fun τ => ⟨haf _, fun i => ⟨?_, ?_⟩, fun i => ?_, ?_, fun hg => ?_⟩⟩
  · have := comap O (LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω)
      fun y => algebraMap O Ω (χ τ (y i))).toAddMonoidHom (fun a v => map_smul (LinearMap.toSpanSingleton Ω
        ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))) a v)
      (sup O h.famM (sub O (vanSub Ω F n ((i : ℕ) + 1))))
    exact this
  · have := comap O ((LinearMap.toSpanSingleton Ω ((Fin n → F) → Ω)
      fun y => algebraMap O Ω (χ τ (y i))).toAddMonoidHom.prodMap (AddMonoidHom.id (Fin (r τ) → Ω)))
      (fun a v => Prod.ext (map_smul (LinearMap.toSpanSingleton Ω
        ((Fin n → F) → Ω) fun y => algebraMap O Ω (χ τ (y i))) a v.1) rfl)
      (sup O (h.fam τ).2.2.2.2.2.2 (prod O (sub O (vanSub Ω F n ((i : ℕ) + 1))) (bot O)))
    exact this
  · have := map O (AddMonoidHom.snd ((Fin n → F) → Ω) (Fin (r τ) → Ω)) (fun a v => rfl)
      (inf O (h.fam τ).2.2.2.2.2.2 (prod O (sub O (vanSub Ω F n i)) (top O)))
    exact this
  · exact dual O (h.fam τ).1 fun c hc => exists_gens _ _ _ ((h.base c hc).free τ).1
  · have h01 := (h.char.2.2.2.2 τ)
    have hh : IsLatFamily O x (fun c => (D c).hh (chartRing O (mseg x) c) p
        (fun a => algebraMap O Ω (χ τ a))) :=
      dual O (haf _) fun c hc => af_gens (D c) _ p _ _ (by simp [h01.1]) (by simp [h01.2])
        (hg c hc).l1 ((hg c hc).lin τ)
    refine ⟨hh, ?_⟩
    have := map O (AddMonoidHom.snd (Fin n → Ω) (Fin (s τ) → Ω)) (fun a v => rfl)
      (inf O (h.fam τ).2.2.2.2.2.1 (prod O hh (top O)))
    exact this

end GlobalTheory.CompanionTheory.Ar.Num.FamConstr
