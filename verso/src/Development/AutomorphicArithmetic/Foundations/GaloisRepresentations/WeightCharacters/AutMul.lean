import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Use extensionality with `g`. Both sides reduce to the same expression.
-/
private theorem RU_mul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (x : UA E a) (φ ψ : UA E a → ℂ) :
    RU E a x (fun g => φ g * ψ g) = RU E a x φ * RU E a x ψ := by
  ext g
  rfl

/- English proof (translation)
Introduce `E _ _ _ a φ ψ hφ hψ`. Use `⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ (γ * g) * ψ (γ * g) = φ g * ψ g`. Rewrite using `[hφ.left γ hγ, hψ.left γ hγ]`. Use `isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) (fun g => φ g * ψ g) ?_` and prove the remaining obligations.

Use `Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `RU E a 1 φ = φ`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `RU E a 1 ψ = ψ`. Simplify using the standard rewrite rules.

Establish `h1 : RU E a k φ = φ` using `hk.1`. Establish `h2 : RU E a k ψ = ψ` using `hk.2`. Express the relevant statement in the definitionally equal form `RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g`. Rewrite using `[RU_mul', h1, h2]`. Both sides reduce to the same expression.

Use `haveI := hφ.kfin haveI := hψ.kfin`. Establish `f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG` using `Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance`. Establish `f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG` using `Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance`. Use `haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) * Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) := Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)`. Use `Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) * Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, rfl⟩`. Express the relevant statement in the definitionally equal form `RU E a k (fun g => φ g * ψ g) ∈ _`. Rewrite using `[RU_mul']`. Conclude with `Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem UpperTheory.Gal.Wt.autMul_of :
    UpperTheory.Gal.Wt.AutMul := by
  intro E _ _ _ a φ ψ hφ hψ
  refine ⟨hφ.cont.mul hψ.cont, fun γ hγ g => ?_, ?_, ?_⟩
  · change φ (γ * g) * ψ (γ * g) = φ g * ψ g
    rw [hφ.left γ hγ, hψ.left γ hγ]
  · refine isOpen_stab_of_mem_nhds ((RU E a).comp (finU E a).subtype) (fun g => φ g * ψ g) ?_
    refine Filter.mem_of_superset ((hφ.level.inter hψ.level).mem_nhds ⟨?_, ?_⟩) fun k hk => ?_
    · change RU E a 1 φ = φ
      simp
    · change RU E a 1 ψ = ψ
      simp
    · have h1 : RU E a k φ = φ := hk.1
      have h2 : RU E a k ψ = ψ := hk.2
      change RU E a k (fun g => φ g * ψ g) = fun g => φ g * ψ g
      rw [RU_mul', h1, h2]
      rfl
  · haveI := hφ.kfin
    haveI := hψ.kfin
    have f1 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    have f2 : (Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)).FG :=
      Submodule.fg_iff_finiteDimensional _ |>.2 inferInstance
    haveI : FiniteDimensional ℂ ↥(Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) :=
      Submodule.fg_iff_finiteDimensional _ |>.1 (f1.mul f2)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range fun k : infU E a => RU E a k φ) *
        Submodule.span ℂ (Set.range fun k : infU E a => RU E a k ψ)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    change RU E a k (fun g => φ g * ψ g) ∈ _
    rw [RU_mul']
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨k, rfl⟩) (Submodule.subset_span ⟨k, rfl⟩)
