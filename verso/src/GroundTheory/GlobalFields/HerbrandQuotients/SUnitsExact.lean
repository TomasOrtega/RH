import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import GroundTheory.GlobalFields.HerbrandQuotients.Cyclic
import GroundTheory.GlobalFields.HerbrandQuotients.CycTate

namespace GroundTheory.Global

open GroundTheory.GroupCoh

variable {G A B C : Type*} [Group G] [Fintype G] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C]

/- English proof (translation)
The claim follows from `hasCyclicHerbrand_of_finite ρ hσ`.
-/
theorem hasHerbrandQuotient_cycSubOne_of_finite [Module.Finite ℤ A] (ρ : Representation ℤ G A)
    {σ : G} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) :=
  hasCyclicHerbrand_of_finite ρ hσ

/- English proof (translation)
Establish `hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩`. Establish `hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range`. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩`. Establish `: p.range.FiniteIndex` using `AddSubgroup.finiteIndex_of_finite_quotient`. Establish `hR` using `(hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)).2 hC`. Establish `hex' : Function.Exact i p.rangeRestrict`. Introduce `b`.

Rewrite using `[← hex b]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify using `using congrArg Subtype.val h`. Introduce `h`.

Conclude with `Subtype.ext (by simpa using h)`. Rewrite using `[cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]`. Conclude with `herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex' (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG]) (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG]) (fun b => Subtype.ext (by simp [cycSubOne_apply, hpG])) (fun b => S …`.
-/
theorem cycHerbrand_eq_mul_of_exact (ρA : Representation ℤ G A) (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {i : A →+ B} {p : B →+ C} (hi : Function.Injective i)
    (hex : Function.Exact i p) [Finite (C ⧸ p.range)]
    (hiG : ∀ g a, i (ρA g a) = ρB g (i a)) (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρA σ * cycHerbrand ρC σ := by
  have hfS : ∀ x ∈ p.range, cycSubOne ρC σ x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycSubOne ρB σ b, by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]⟩
  have hgS : ∀ x ∈ p.range, cycNorm ρC x ∈ p.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨cycNorm ρB b, by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]⟩
  have : p.range.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  have hR := (hasHerbrandQuotient_restrictEnd_iff p.range hfS hgS (cycSubOne_cycNorm ρC σ)
    (cycNorm_cycSubOne ρC σ)).2 hC
  have hex' : Function.Exact i p.rangeRestrict := by
    intro b
    rw [← hex b]
    constructor
    · intro h
      simpa using congrArg Subtype.val h
    · intro h
      exact Subtype.ext (by simpa using h)
  rw [cycHerbrand, cycHerbrand, cycHerbrand, ← herbrandQuotient_restrictEnd p.range hfS hgS
    (cycSubOne_cycNorm ρC σ) (cycNorm_cycSubOne ρC σ)]
  exact herbrandQuotient_eq_mul_of_shortExact hi p.rangeRestrict_surjective hex'
    (fun a => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hiG])
    (fun a => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hiG])
    (fun b => Subtype.ext (by simp [cycSubOne_apply, hpG]))
    (fun b => Subtype.ext (by simp [cycNorm_apply, hpG, map_sum]))
    (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hR

/- English proof (translation)
Establish `hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker`. Introduce `x hx`. Rewrite `hx`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite using `[cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]`. Establish `hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker`.

Introduce `x hx`. Rewrite `hx`, the goal using `[AddMonoidHom.mem_ker]`. Rewrite using `[cycNorm_apply, map_sum]`. Simplify using `[hpG, hx]`. Establish `hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK (restrictEnd (cycNorm ρB) p.ker hgK x) = 0` using `fun x => Subtype.ext (by simp [cycSubOne_cycNorm])`.

Establish `hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0` using `fun x => Subtype.ext (by simp [cycNorm_cycSubOne])`. Establish `hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK) (restrictEnd (cycNorm ρB) p.ker hgK)` using `hasHerbrandQuotient_of_finite _ _`. Establish `hex : Function.Exact p.ker.subtype p`. Introduce `b`. Simplify using the standard rewrite rules.

Rewrite using `[cycHerbrand, cycHerbrand, herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex (fun _ => rfl) (fun _ => rfl) (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG]) (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG]) (cycSubOne_cyc …`.
-/
theorem cycHerbrand_eq_of_surjective_of_finite_ker (ρB : Representation ℤ G B)
    (ρC : Representation ℤ G C) (σ : G) {p : B →+ C} (hp : Function.Surjective p)
    [Finite p.ker] (hpG : ∀ g b, p (ρB g b) = ρC g (p b))
    (hC : HasHerbrandQuotient (cycSubOne ρC σ) (cycNorm ρC)) :
    cycHerbrand ρB σ = cycHerbrand ρC σ := by
  have hfK : ∀ x ∈ p.ker, cycSubOne ρB σ x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycSubOne_apply, map_sub, hpG, hx, map_zero, sub_zero]
  have hgK : ∀ x ∈ p.ker, cycNorm ρB x ∈ p.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx ⊢
    rw [cycNorm_apply, map_sum]
    simp [hpG, hx]
  have hfgK : ∀ x, restrictEnd (cycSubOne ρB σ) p.ker hfK
      (restrictEnd (cycNorm ρB) p.ker hgK x) = 0 := fun x =>
    Subtype.ext (by simp [cycSubOne_cycNorm])
  have hgfK : ∀ x, restrictEnd (cycNorm ρB) p.ker hgK
      (restrictEnd (cycSubOne ρB σ) p.ker hfK x) = 0 := fun x =>
    Subtype.ext (by simp [cycNorm_cycSubOne])
  have hA : HasHerbrandQuotient (restrictEnd (cycSubOne ρB σ) p.ker hfK)
      (restrictEnd (cycNorm ρB) p.ker hgK) := hasHerbrandQuotient_of_finite _ _
  have hex : Function.Exact p.ker.subtype p := by
    intro b
    simp
  rw [cycHerbrand, cycHerbrand,
    herbrandQuotient_eq_mul_of_shortExact p.ker.subtype_injective hp hex
      (fun _ => rfl) (fun _ => rfl)
      (fun b => by rw [cycSubOne_apply, cycSubOne_apply, map_sub, hpG])
      (fun b => by rw [cycNorm_apply, cycNorm_apply, map_sum]; simp only [hpG])
      (cycSubOne_cycNorm ρB σ) (cycNorm_cycSubOne ρB σ) hA hC,
    herbrandQuotient_eq_one_of_finite hfgK hgfK, one_mul]

/- English proof (translation)
Establish `: Finite (B ⧸ (AddMonoidHom.snd A B).range)`. Rewrite using `[AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]`. Use `infer_instance`. Use `cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B) (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_) (fun g b => rfl) hA hB` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩`.

Simplify using `only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Conclude with `⟨a, rfl, rfl⟩`. Introduce and unpack `⟨a', -, rfl⟩`.

Both sides reduce to the same expression. Conclude with `Prod.ext rfl (map_zero (ρB g)).symm`.
-/
theorem cycHerbrand_prod (ρA : Representation ℤ G A) (ρB : Representation ℤ G B) (σ : G)
    (hA : HasHerbrandQuotient (cycSubOne ρA σ) (cycNorm ρA))
    (hB : HasHerbrandQuotient (cycSubOne ρB σ) (cycNorm ρB)) :
    cycHerbrand (ρA.prod ρB) σ = cycHerbrand ρA σ * cycHerbrand ρB σ := by
  have : Finite (B ⧸ (AddMonoidHom.snd A B).range) := by
    rw [AddMonoidHom.range_eq_top.2 (fun b => ⟨(0, b), rfl⟩)]
    infer_instance
  refine cycHerbrand_eq_mul_of_exact ρA (ρA.prod ρB) ρB σ (i := AddMonoidHom.inl A B)
    (p := AddMonoidHom.snd A B) (fun a a' h => congrArg Prod.fst h) ?_ (fun g a => ?_)
    (fun g b => rfl) hA hB
  · rintro ⟨a, b⟩
    simp only [AddMonoidHom.coe_snd, Set.mem_range, AddMonoidHom.inl_apply, Prod.ext_iff]
    constructor
    · rintro rfl
      exact ⟨a, rfl, rfl⟩
    · rintro ⟨a', -, rfl⟩
      rfl
  · exact Prod.ext rfl (map_zero (ρB g)).symm

end GroundTheory.Global
