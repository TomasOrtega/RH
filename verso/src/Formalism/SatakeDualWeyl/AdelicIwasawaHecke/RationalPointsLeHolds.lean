import Formalism.SatakeDualWeyl.Statement

noncomputable section

open Matrix TensorProduct

namespace Formalism.UG.P

open Formalism.UG

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cT, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `(RingHom.congr_fun h (M j i)).symm`.
-/
theorem cT_map {A B : Type} [CommRing A] [CommRing B] (σ : A →+* A) (σ' : B →+* B)
    (φ : A →+* B) (h : φ.comp σ = σ'.comp φ) {m p : Type} (M : Matrix m p A) :
    cT σ' (M.map φ) = (cT σ M).map φ := by
  ext i j
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply]
  exact (RingHom.congr_fun h (M j i)).symm

/- English proof (translation)
Introduce `A B _ _ n _ _ σ σ' φ h J g hg`. Establish `hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J` using `hg`. Use `show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) = J.map φ`. Establish `e : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ` using `rfl`. Rewrite using `[e, cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']`.
-/
theorem base_change_mem_holds : Formalism.UG.BCMem := by
  intro A B _ _ n _ _ σ σ' φ h J g hg
  have hg' : cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show cT σ' ((bc φ g : GL n B) : Matrix n n B) * J.map φ * ((bc φ g : GL n B) : Matrix n n B) =
    J.map φ
  have e : ((bc φ g : GL n B) : Matrix n n B) = (g : Matrix n n A).map φ := rfl
  rw [e, cT_map σ σ' φ h, ← Matrix.map_mul, ← Matrix.map_mul, hg']

/- English proof (translation)
Introduce `F E _ _ _ n _ _ σ J R _ _ x hx`. Take `⟨g, hg, rfl⟩` from `Subgroup.mem_map.mp hx`. Establish `hc : (inclE (F` using `F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE (F := F) R) := by`. Use extensionality with `e`. Simplify using `[inclE, sigR, Algebra.TensorProduct.map_tmul]`.

Conclude with `base_change_mem_holds E (E ⊗[F] R) n (σ : E →+* E) (sigR σ R) (inclE (F := F) R) hc J g hg`.
-/
theorem rational_points_le_holds : Formalism.UG.RatPtsLe := by
  intro F E _ _ _ n _ _ σ J R _ _ x hx
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hx
  have hc : (inclE (F := F) R).comp (σ : E →+* E) = (sigR σ R).comp (inclE (F := F) R) := by
    ext e
    simp [inclE, sigR, Algebra.TensorProduct.map_tmul]
  exact base_change_mem_holds E (E ⊗[F] R) n (σ : E →+* E) (sigR σ R) (inclE (F := F) R) hc J g hg

end Formalism.UG.P
