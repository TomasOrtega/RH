import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development

open MvPolynomial

noncomputable section

namespace PI.TOW.LiftW

open PI.TO PI.TOW

variable {K : Type} [CommRing K] {n' k : ℕ}

/- English proof (translation)
Introduce `a c h`. Conclude with `(Prod.mk.inj h).2`.
-/
theorem inj (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by
  intro a c h
  exact (Prod.mk.inj h).2

/- English proof (translation)
Simplify `pderiv_rename (inj (k := k) t) b W` using `[embS]`.
-/
theorem pderiv_embS (t : Fin n') (b : Fin k) (W : MvPolynomial (Fin k) K) :
    pderiv (t, b) (embS K t W) = embS K t (pderiv b W) := by
  simpa [embS] using pderiv_rename (inj (k := k) t) b W

/- English proof (translation)
Introduce `hm`. Establish `h2 : (t, b) ∈ W.vars.image (fun c : Fin k => (a, c))` using `vars_rename (fun c : Fin k => (a, c)) W hm`. Rewrite `h2` using `[Finset.mem_image]`. Take `⟨c, -, hc⟩` from `h2`. Conclude with `h (congrArg Prod.fst hc)`.
-/
theorem notMem_vars_embS {t a : Fin n'} (h : a ≠ t) (b : Fin k) (W : MvPolynomial (Fin k) K) :
    (t, b) ∉ (embS K a W).vars := by
  intro hm
  have h2 : (t, b) ∈ W.vars.image (fun c : Fin k => (a, c)) :=
    vars_rename (fun c : Fin k => (a, c)) W hm
  rw [Finset.mem_image] at h2
  obtain ⟨c, -, hc⟩ := h2
  exact h (congrArg Prod.fst hc)

/- English proof (translation)
Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert s T hs ih`. Rewrite using `[Finset.prod_insert hs, Derivation.leibniz]`. Establish `hst : s ≠ t` using `fun e => ht (e ▸ Finset.mem_insert_self s T)`.

Rewrite using `[ih (fun h => ht (Finset.mem_insert_of_mem h)), pderiv_eq_zero_of_notMem_vars (notMem_vars_embS hst b (H s))]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_prod_ne (t : Fin n') (b : Fin k) (T : Finset (Fin n')) (ht : t ∉ T)
    (H : Fin n' → MvPolynomial (Fin k) K) : pderiv (t, b) (∏ s ∈ T, embS K s (H s)) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Derivation.leibniz]
    have hst : s ≠ t := fun e => ht (e ▸ Finset.mem_insert_self s T)
    rw [ih (fun h => ht (Finset.mem_insert_of_mem h)),
      pderiv_eq_zero_of_notMem_vars (notMem_vars_embS hst b (H s))]
    simp

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp [opWord, liftW, word1]`. Consider the case `cons y l ih`. Establish `e1 : opWord (liftW t (y :: l)) (embS K t F * R) = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R))`. Simplify using `[opWord, liftW]`.

Establish `e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F)`. Simplify using `[word1]`. Rewrite using `[e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]`. Simplify using `[embS, map_mul, rename_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opWord_liftW (t : Fin n') (l : List (Fin k × Fin k)) (F : MvPolynomial (Fin k) K)
    (R : MvPolynomial (Fin n' × Fin k) K) (hR : ∀ b, pderiv (t, b) R = 0) :
    opWord (liftW t l) (embS K t F * R) = embS K t (word1 l F) * R := by
  induction l with
  | nil => simp [opWord, liftW, word1]
  | cons y l ih =>
    have e1 : opWord (liftW t (y :: l)) (embS K t F * R)
        = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R)) := by
      simp [opWord, liftW]
    have e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F) := by
      simp [word1]
    rw [e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]
    simp [embS, map_mul, rename_X]
    ring

/- English proof (translation)
Simplify using `[opWord, List.foldr_append]`.
-/
theorem opWord_append (l₁ l₂ : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (l₁ ++ l₂) f = opWord l₁ (opWord l₂ f) := by
  simp [opWord, List.foldr_append]

/- English proof (translation)
Proceed by induction on `ts with`. Consider the case `nil => simp [opWord]`. Consider the case `cons t ts ih`. Rewrite `hts` using `[List.nodup_cons]`. Rewrite using `[List.flatMap_cons, opWord_append, ih hts.2]`.

Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t), ← Finset.mul_prod_erase Finset.univ (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]`. Simplify using `only [if_neg hts.1, List.mem_cons, true_or, if_true]`. Rewrite using `[opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]`. Use `congr 1`. Use `Finset.prod_congr rfl fun s hs => ?_` and prove the remaining obligations.

Establish `hne : s ≠ t` using `Finset.ne_of_mem_erase hs`. Simplify using `[hne]`.
-/
theorem main_list (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by
  classical
  induction ts with
  | nil => simp [opWord]
  | cons t ts ih =>
    rw [List.nodup_cons] at hts
    rw [List.flatMap_cons, opWord_append, ih hts.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase Finset.univ
        (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]
    simp only [if_neg hts.1, List.mem_cons, true_or, if_true]
    rw [opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ t := Finset.ne_of_mem_erase hs
    simp [hne]

/- English proof (translation)
Introduce `K _ n' k w F`. Establish `h` using `main_list w F (List.finRange n') (List.nodup_finRange n')`. Simplify `h` using `[concatW, List.mem_finRange]`.
-/
theorem stepLift : StepLift := by
  intro K _ n' k w F
  have h := main_list w F (List.finRange n') (List.nodup_finRange n')
  simpa [concatW, List.mem_finRange] using h

end PI.TOW.LiftW
