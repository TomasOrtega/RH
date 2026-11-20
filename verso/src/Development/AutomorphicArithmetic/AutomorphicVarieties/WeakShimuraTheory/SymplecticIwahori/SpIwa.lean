import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.AdjMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SymplecticIwahori.GramCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Pp

/- English proof (translation)
Introduce `F _ V h hh`. Set `f : V →+* F` to `V.subtype`. Set `hU : GL (Fin 4) F` to `⟨h, adj h, mul_adj_self hh, adj_mul_self hh⟩`. Take `⟨k0, b, hb, hk⟩` from `GlobalTheory.ValIwasawa.iwasawa V F 4 hU`. Establish `hbU : IsUp (b : M4 F)` using `(isUp_iff _).mpr hb`.

Establish `hbi : IsUp ((b⁻¹ : GL (Fin 4) F) : M4 F)` using `IsUp_inv hbU`. Establish `hKmap : (k0 : M4 V).map f = h * ((b⁻¹ : GL (Fin 4) F) : M4 F)`. Establish `h1 : (hU : M4 F) = ((Matrix.GeneralLinearGroup.map (algebraMap V F) k0 : GL (Fin 4) F) : M4 F) * (b : M4 F)`. Rewrite using `[hk]`. Both sides reduce to the same expression.

Establish `h2 : (hU : M4 F) = h` using `rfl`. Rewrite `h1` using `[h2]`. Rewrite using `[h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Both sides reduce to the same expression. Establish `hadjh : adj (h * ((b⁻¹ : GL (Fin 4) F) : M4 F)) * h = adj ((b⁻¹ : GL (Fin 4) F) : M4 F)`.

Rewrite using `[(grp F).1, Matrix.mul_assoc, adj_mul_self hh, Matrix.mul_one]`. Establish `hmapadj : ∀ X : M4 V, adj (X.map f) = (adj X).map f` using `fun X => (grp V).2.2.2.2.2.1 F f X`. Establish `upMap : ∀ X : M4 V, IsUp (X.map f) → IsUp X`. Introduce `X hX i j hij`. Establish `hz` using `hX i j hij`.

Simplify `hz` using `[f]`. Establish `hQ : IsUp (adj (k0 : M4 V) * (k0 : M4 V))`. Apply `upMap` to reduce the goal to its premises. Rewrite using `[Matrix.map_mul, ← hmapadj, hKmap, (grp F).1, Matrix.mul_assoc, ← Matrix.mul_assoc (adj h), adj_mul_self hh, Matrix.one_mul]`. Conclude with `IsUp_mul (IsUp_adj hbi) hbi`.

Take `⟨t, ht, hkt⟩` from `gram k0 hQ`. Use `⟨(k0 : M4 V) * (t : M4 V), hkt, ?_⟩` and prove the remaining obligations. Establish `htU : IsUp ((t : M4 V).map f)`. Introduce `i j hij`. Simplify using `[ht i j hij]`.

Rewrite using `[Matrix.map_mul, (grp F).1, hKmap, Matrix.mul_assoc, hadjh]`. Conclude with `IsUp_mul (IsUp_adj htU) (IsUp_adj hbi)`.
-/
theorem UpperTheory.V.Ws.Pp.spIwa :
    ∀ {F : Type} [Field F] (V : ValuationSubring F) (h : M4 F), IsGSp 1 h → ∃ k : M4 V, IsGSp 1 k ∧ IsUp (adj (k.map V.subtype) * h) := by
  intro F _ V h hh
  let f : V →+* F := V.subtype
  let hU : GL (Fin 4) F := ⟨h, adj h, mul_adj_self hh, adj_mul_self hh⟩
  obtain ⟨k0, b, hb, hk⟩ := GlobalTheory.ValIwasawa.iwasawa V F 4 hU
  have hbU : IsUp (b : M4 F) := (isUp_iff _).mpr hb
  have hbi : IsUp ((b⁻¹ : GL (Fin 4) F) : M4 F) := IsUp_inv hbU
  have hKmap : (k0 : M4 V).map f = h * ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    have h1 : (hU : M4 F) =
        ((Matrix.GeneralLinearGroup.map (algebraMap V F) k0 : GL (Fin 4) F) : M4 F) * (b : M4 F) := by
      rw [hk]
      rfl
    have h2 : (hU : M4 F) = h := rfl
    rw [h2] at h1
    rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rfl
  have hadjh : adj (h * ((b⁻¹ : GL (Fin 4) F) : M4 F)) * h = adj ((b⁻¹ : GL (Fin 4) F) : M4 F) := by
    rw [(grp F).1, Matrix.mul_assoc, adj_mul_self hh, Matrix.mul_one]
  have hmapadj : ∀ X : M4 V, adj (X.map f) = (adj X).map f := fun X => (grp V).2.2.2.2.2.1 F f X
  have upMap : ∀ X : M4 V, IsUp (X.map f) → IsUp X := by
    intro X hX i j hij
    have hz := hX i j hij
    simpa [f] using hz
  have hQ : IsUp (adj (k0 : M4 V) * (k0 : M4 V)) := by
    apply upMap
    rw [Matrix.map_mul, ← hmapadj, hKmap, (grp F).1, Matrix.mul_assoc,
      ← Matrix.mul_assoc (adj h), adj_mul_self hh, Matrix.one_mul]
    exact IsUp_mul (IsUp_adj hbi) hbi
  obtain ⟨t, ht, hkt⟩ := gram k0 hQ
  refine ⟨(k0 : M4 V) * (t : M4 V), hkt, ?_⟩
  have htU : IsUp ((t : M4 V).map f) := by
    intro i j hij
    simp [ht i j hij]
  rw [Matrix.map_mul, (grp F).1, hKmap, Matrix.mul_assoc, hadjh]
  exact IsUp_mul (IsUp_adj htU) (IsUp_adj hbi)
