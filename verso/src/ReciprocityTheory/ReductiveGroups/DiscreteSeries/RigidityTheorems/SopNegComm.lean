import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DefsRep

noncomputable section

open Finset Matrix WithLp

namespace ReciprocityTheory.ChartRestriction.DS

namespace USum

variable {n : ℕ}

section Ops

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def sop (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) : WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).symm.toContinuousLinearMap ∘L
    ((A.prodMap B) ∘L (WithLp.prodContinuousLinearEquiv 2 ℂ H₁ H₂).toContinuousLinearMap)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ofLp_sop (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    ofLp (sop A B x) = (A (ofLp x).1, B (ofLp x).2) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sop_apply (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop A B x = toLp 2 (A (ofLp x).1, B (ofLp x).2) := rfl

/- English proof (translation)
Rewrite using `[WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]`. Use `show √(‖A (ofLp x).1‖ ^ 2 + ‖B (ofLp x).2‖ ^ 2) = √(‖(ofLp x).1‖ ^ 2 + ‖(ofLp x).2‖ ^ 2)`. Rewrite using `[hA, hB]`.
-/
theorem norm_sop {A : H₁ →L[ℂ] H₁} {B : H₂ →L[ℂ] H₂} (hA : ∀ v, ‖A v‖ = ‖v‖)
    (hB : ∀ v, ‖B v‖ = ‖v‖) (x : WithLp 2 (H₁ × H₂)) : ‖sop A B x‖ = ‖x‖ := by
  rw [WithLp.prod_norm_eq_of_L2, WithLp.prod_norm_eq_of_L2]
  show √(‖A (ofLp x).1‖ ^ 2 + ‖B (ofLp x).2‖ ^ 2) = √(‖(ofLp x).1‖ ^ 2 + ‖(ofLp x).2‖ ^ 2)
  rw [hA, hB]

/- English proof (translation)
Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem sop_one : sop (1 : H₁ →L[ℂ] H₁) (1 : H₂ →L[ℂ] H₂) = 1 := by
  ext x; rfl

/- English proof (translation)
Use extensionality with `x`. Both sides reduce to the same expression.
-/
theorem sop_comp (A A' : H₁ →L[ℂ] H₁) (B B' : H₂ →L[ℂ] H₂) :
    sop (A.comp A') (B.comp B') = (sop A B).comp (sop A' B') := by
  ext x; rfl

/- English proof (translation)
Simplify using `only [sop_apply, WithLp.ofLp_toLp]`. Simplify using the standard rewrite rules.
-/
theorem sop_neg_comm (A : H₁ →L[ℂ] H₁) (B : H₂ →L[ℂ] H₂) (x : WithLp 2 (H₁ × H₂)) :
    sop 1 (-1) (sop A B x) = sop A B (sop 1 (-1) x) := by
  simp only [sop_apply, WithLp.ofLp_toLp]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inner_sum (x y : WithLp 2 (H₁ × H₂)) :
    inner ℂ x y = inner ℂ (ofLp x).1 (ofLp y).1 + inner ℂ (ofLp x).2 (ofLp y).2 := rfl

def sD (D₁ : Submodule ℂ H₁) (D₂ : Submodule ℂ H₂) : Submodule ℂ (WithLp 2 (H₁ × H₂)) :=
  (D₁.prod D₂).comap (WithLp.linearEquiv 2 ℂ (H₁ × H₂)).toLinearMap

variable {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}

def toP : sD D₁ D₂ →ₗ[ℂ] D₁ × D₂ where
  toFun x := (⟨(ofLp (x : WithLp 2 (H₁ × H₂))).1, x.2.1⟩, ⟨(ofLp (x : WithLp 2 (H₁ × H₂))).2, x.2.2⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofP : D₁ × D₂ →ₗ[ℂ] sD D₁ D₂ where
  toFun p := ⟨toLp 2 ((p.1 : H₁), (p.2 : H₂)), p.1.2, p.2.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toPrimitive_ofPrimitive (p : D₁ × D₂) : toP (ofP p) = p := rfl

def lift (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) : Module.End ℂ (sD D₁ D₂) :=
  ofP ∘ₗ (F₁.prodMap F₂) ∘ₗ toP

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lift_ofP (F₁ : Module.End ℂ D₁) (F₂ : Module.End ℂ D₂) (p : D₁ × D₂) :
    lift F₁ F₂ (ofP p) = ofP (F₁ p.1, F₂ p.2) := rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => rfl`.
-/
theorem lift_mul (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ * G₁) (F₂ * G₂) = lift F₁ F₂ * lift G₁ G₂ := LinearMap.ext fun _ => rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => rfl`.
-/
theorem lift_sub (F₁ G₁ : Module.End ℂ D₁) (F₂ G₂ : Module.End ℂ D₂) :
    lift (F₁ - G₁) (F₂ - G₂) = lift F₁ F₂ - lift G₁ G₂ := LinearMap.ext fun _ => rfl

/- English proof (translation)
The claim follows from `LinearMap.ext fun _ => rfl`.
-/
theorem lift_zero : lift (0 : Module.End ℂ D₁) (0 : Module.End ℂ D₂) = 0 :=
  LinearMap.ext fun _ => rfl

def liftL : (Module.End ℂ D₁ × Module.End ℂ D₂) →ₗ[ℂ] Module.End ℂ (sD D₁ D₂) where
  toFun p := lift p.1 p.2
  map_add' _ _ := LinearMap.ext fun _ => rfl
  map_smul' _ _ := LinearMap.ext fun _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem liftL_apply (p : Module.End ℂ D₁ × Module.End ℂ D₂) : liftL p = lift p.1 p.2 := rfl

def sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    Fin n → Fin n → Module.End ℂ (sD D₁ D₂) :=
  fun a b => lift (E₁ a b) (E₂ a b)

/- English proof (translation)
Establish `h : ∀ a b, X a b • sE E₁ E₂ a b = liftL (X a b • (E₁ a b, E₂ a b))`. Introduce `a b`. Rewrite using `[map_smul]`. Both sides reduce to the same expression. Unfold `actM`.

Simplify using `only [h, ← map_sum]`. Rewrite using `[liftL_apply]`. Use `congr 1`. Simplify using `[Prod.fst_sum]`. Simplify using `[Prod.snd_sum]`.
-/
theorem actM_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂)
    (X : Matrix (Fin n) (Fin n) ℂ) : actM (sE E₁ E₂) X = lift (actM E₁ X) (actM E₂ X) := by
  have h : ∀ a b, X a b • sE E₁ E₂ a b = liftL (X a b • (E₁ a b, E₂ a b)) := by
    intro a b; rw [map_smul]; rfl
  unfold actM
  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

/- English proof (translation)
Establish `h : ∀ a b, sE E₁ E₂ a b * sE E₁ E₂ b a = liftL (E₁ a b * E₁ b a, E₂ a b * E₂ b a)`. Introduce `a b`. Rewrite using `[liftL_apply]`. Conclude with `(lift_mul _ _ _ _).symm`. Unfold `casimir`.

Simplify using `only [h, ← map_sum]`. Rewrite using `[liftL_apply]`. Use `congr 1`. Simplify using `[Prod.fst_sum]`. Simplify using `[Prod.snd_sum]`.
-/
theorem casimir_sE (E₁ : Fin n → Fin n → Module.End ℂ D₁) (E₂ : Fin n → Fin n → Module.End ℂ D₂) :
    casimir (sE E₁ E₂) = lift (casimir E₁) (casimir E₂) := by
  have h : ∀ a b, sE E₁ E₂ a b * sE E₁ E₂ b a = liftL (E₁ a b * E₁ b a, E₂ a b * E₂ b a) := by
    intro a b; rw [liftL_apply]; exact (lift_mul _ _ _ _).symm
  unfold casimir
  simp only [h, ← map_sum]
  rw [liftL_apply]
  congr 1
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum]

section Rep

variable {ε : Fin n → Bool}
  {σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)} {σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)}

def sσ (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H₁ →L[ℂ] H₁)) (σ₂ : Matrix (Fin n) (Fin n) ℂ → (H₂ →L[ℂ] H₂)) :
    Matrix (Fin n) (Fin n) ℂ → (WithLp 2 (H₁ × H₂) →L[ℂ] WithLp 2 (H₁ × H₂)) :=
  fun g => sop (σ₁ g) (σ₂ g)

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show sop (σ₁ 1) (σ₂ 1) = 1`. Rewrite using `[h₁.1.1, h₂.1.1]`. Conclude with `sop_one`. Introduce `a ha b hb show sop (σ₁ (a * b)) (σ₂ (a * b)) = (sop (σ₁ a) (σ₂ a)).comp (sop (σ₁ b) (σ₂ b))`.

Rewrite using `[h₁.1.2 a ha b hb, h₂.1.2 a ha b hb, sop_comp]`. Introduce `g hg v`. Conclude with `norm_sop (h₁.2.1 g hg) (h₂.2.1 g hg) v`. Introduce `v`. Establish `hc` using `((h₁.2.2 (ofLp v).1).prodMk (h₂.2.2 (ofLp v).2))`.

Conclude with `(WithLp.prod_continuous_toLp 2 H₁ H₂).comp_continuousOn hc`.
-/
theorem isURepOn_sσ {G : Set (Matrix (Fin n) (Fin n) ℂ)} (h₁ : IsURepOn G σ₁) (h₂ : IsURepOn G σ₂) :
    IsURepOn G (sσ σ₁ σ₂) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show sop (σ₁ 1) (σ₂ 1) = 1
    rw [h₁.1.1, h₂.1.1]; exact sop_one
  · intro a ha b hb
    show sop (σ₁ (a * b)) (σ₂ (a * b)) = (sop (σ₁ a) (σ₂ a)).comp (sop (σ₁ b) (σ₂ b))
    rw [h₁.1.2 a ha b hb, h₂.1.2 a ha b hb, sop_comp]
  · intro g hg v
    exact norm_sop (h₁.2.1 g hg) (h₂.2.1 g hg) v
  · intro v
    have hc := ((h₁.2.2 (ofLp v).1).prodMk (h₂.2.2 (ofLp v).2))
    exact (WithLp.prod_continuous_toLp 2 H₁ H₂).comp_continuousOn hc

/- English proof (translation)
Introduce `a b c d`. Establish `e1` using `hD₁.glRep a b c d`. Establish `e2` using `hD₂.glRep a b c d`. Use `show lift (E₁ a b) (E₂ a b) * lift (E₁ c d) (E₂ c d) - lift (E₁ c d) (E₂ c d) * lift (E₁ a b) (E₂ a b) = (if b = c then lift (E₁ a d) (E₂ a d) else 0) - (if d = a then lift (E₁ c b) (E₂ c b) else 0)`. Rewrite using `[← lift_mul, ← lift_mul, ← lift_sub, e1, e2]`.

Apply the tactic sequence `split_ifs <;> rw [lift_sub] <;> simp only [lift_zero]`. Use `kStable := by`. Introduce `k hk v hv`. Conclude with `⟨hD₁.kStable k hk _ hv.1, hD₂.kStable k hk _ hv.2⟩`. Use `deriv := by`.

Introduce `X hX v`. Establish `h1` using `hD₁.deriv X hX (toP v).1`. Establish `h2` using `hD₂.deriv X hX (toP v).2`. Establish `h3` using `(WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h1.prodMk h2)`. Rewrite using `[actM_sE]`.

Conclude with `h3`.
-/
theorem isDerivedOn_sσ {D₁ : Submodule ℂ H₁} {D₂ : Submodule ℂ H₂}
    {E₁ : Fin n → Fin n → Module.End ℂ D₁} {E₂ : Fin n → Fin n → Module.End ℂ D₂}
    (hD₁ : IsDerivedOn ε σ₁ D₁ E₁) (hD₂ : IsDerivedOn ε σ₂ D₂ E₂) :
    IsDerivedOn ε (sσ σ₁ σ₂) (sD D₁ D₂) (sE E₁ E₂) where
  glRep := by
    intro a b c d
    have e1 := hD₁.glRep a b c d
    have e2 := hD₂.glRep a b c d
    show lift (E₁ a b) (E₂ a b) * lift (E₁ c d) (E₂ c d) - lift (E₁ c d) (E₂ c d) * lift (E₁ a b) (E₂ a b) =
      (if b = c then lift (E₁ a d) (E₂ a d) else 0) - (if d = a then lift (E₁ c b) (E₂ c b) else 0)
    rw [← lift_mul, ← lift_mul, ← lift_sub, e1, e2]
    split_ifs <;> rw [lift_sub] <;> simp only [lift_zero]
  kStable := by
    intro k hk v hv
    exact ⟨hD₁.kStable k hk _ hv.1, hD₂.kStable k hk _ hv.2⟩
  deriv := by
    intro X hX v
    have h1 := hD₁.deriv X hX (toP v).1
    have h2 := hD₂.deriv X hX (toP v).2
    have h3 := (WithLp.prodContinuousLinearEquiv 2 ℝ H₁ H₂).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      (0 : ℝ) (h1.prodMk h2)
    rw [actM_sE]
    exact h3

end Rep

end Ops

end USum

end ReciprocityTheory.ChartRestriction.DS
