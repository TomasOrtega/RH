import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.TraceAlgebra.IsoOfTrace

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.T.Alg.Conj2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Alg

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

def SS (a : Matrix (Fin n) (Fin n) k) : Prop := Module.End.IsSemisimple (Matrix.toLin' a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toLinAlgEquiv'_eq (a : Matrix (Fin n) (Fin n) k) : Matrix.toLinAlgEquiv' a = Matrix.toLin' a := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ss_add {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a + b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_add]
  exact Module.End.IsSemisimple.add_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ss_mul {a b : Matrix (Fin n) (Fin n) k} (h : Commute a b) (ha : SS a) (hb : SS b) : SS (a * b) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, map_mul]
  exact Module.End.IsSemisimple.mul_of_commute (h.map Matrix.toLinAlgEquiv') ha hb

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem ss_algebraMap (c : k) : SS (algebraMap k (Matrix (Fin n) (Fin n) k) c) := by
  unfold SS
  rw [← toLinAlgEquiv'_eq, AlgEquiv.commutes]
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X - C c)
    (Polynomial.irreducible_X_sub_C c).squarefree ?_
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem ss_of_mem {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {z : Matrix (Fin n) (Fin n) k}
    (hz : z ∈ Z) : SS z := by
  obtain ⟨nn, hnn, ss, -, hnil, hsss, hsum⟩ := Module.End.exists_isNilpotent_isSemisimple (K := k) (f := Matrix.toLin' z)
  have hmap : Algebra.adjoin k {Matrix.toLin' z} =
      (Algebra.adjoin k {z}).map (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom := by
    rw [← Algebra.adjoin_image, Set.image_singleton]
    rfl
  rw [hmap] at hnn
  obtain ⟨m, hm, hmn⟩ := Subalgebra.mem_map.1 hnn
  have hmZ : m ∈ Z := Algebra.adjoin_le (Set.singleton_subset_iff.2 hz) hm
  have hmnil : IsNilpotent m := by
    have : IsNilpotent ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).symm nn) := hnil.map _
    rw [← hmn] at this
    simpa using this
  have hm0 : m = 0 := by
    have h1 : IsNilpotent (⟨m, hmZ⟩ : Z) := by
      obtain ⟨e, he⟩ := hmnil
      exact ⟨e, Subtype.ext (by simpa using he)⟩
    have := hZ.2.eq_zero _ h1
    simpa using congrArg Subtype.val this
  have hnn0 : nn = 0 := by rw [← hmn, hm0]; simp
  unfold SS
  rw [hsum, hnn0, zero_add]
  exact hsss

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression. Equip the data with the indicated structure.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Supply the required witnesses or components. Treat this case separately.

Establish an intermediate fact. Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Separate the alternatives or extract the components of the hypothesis. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem conj_of (hiso : IsoOfTrace k) : Conj k := by
  intro n Z hZ s s' hs hs' hss hss' htr
  classical
  set S : Set (Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) :=
    (fun z => (z, z)) '' (Z : Set (Matrix (Fin n) (Fin n) k)) ∪ {(s, s')} with hSdef
  have hcomm : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a := by
    rintro a (⟨z, hz, rfl⟩ | ha) b (⟨w, hw, rfl⟩ | hb)
    · simp [hZ.1 z hz w hw]
    · rw [Set.mem_singleton_iff] at hb; subst hb
      simp [hs z hz, hs' z hz]
    · rw [Set.mem_singleton_iff] at ha; subst ha
      simp [hs w hw, hs' w hw]
    · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  set R := Algebra.adjoin k S with hRdef
  letI : CommRing R := Algebra.adjoinCommRingOfComm k hcomm

  have hRc : ∀ x ∈ R, ∀ y ∈ R, Commute x y := fun x hx y hy =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy fun b hb =>
      (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun a ha => hcomm b hb a ha).symm

  have hRss : ∀ x ∈ R, SS x.1 ∧ SS x.2 := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨ss_of_mem hZ hz, ss_of_mem hZ hz⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨hss, hss'⟩
    | algebraMap c => exact ⟨ss_algebraMap c, ss_algebraMap c⟩
    | add x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_add (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_add (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩
    | mul x y hx hy ihx ihy =>
      have h := hRc x hx y hy
      exact ⟨ss_mul (h.map (RingHom.fst _ _)) ihx.1 ihy.1, ss_mul (h.map (RingHom.snd _ _)) ihx.2 ihy.2⟩

  let f : Z →+* Matrix (Fin n) (Fin n) k := Z.val.toRingHom
  have hform : ∀ x ∈ R, ∃ P : Z[X], x = (P.eval₂ f s, P.eval₂ f s') := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨z, hz, rfl⟩ | hx
      · exact ⟨C ⟨z, hz⟩, by simp [f]⟩
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact ⟨X, by simp⟩
    | algebraMap c =>
      refine ⟨C (algebraMap k Z c), ?_⟩
      simp [f, Prod.algebraMap_apply]
    | add x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      exact ⟨P + Q, by simp [eval₂_add]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨P, rfl⟩ := ihx
      obtain ⟨Q, rfl⟩ := ihy
      refine ⟨P * Q, ?_⟩
      rw [eval₂_mul_noncomm _ _ fun j => ?_, eval₂_mul_noncomm _ _ fun j => ?_]
      · rfl
      · exact hs' (f (Q.coeff j)) (Q.coeff j).2
      · exact hs (f (Q.coeff j)) (Q.coeff j).2
  have htrP : ∀ P : Z[X], trace (P.eval₂ f s) = trace (P.eval₂ f s') := by
    intro P
    rw [eval₂_eq_sum, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, trace_sum, trace_sum]
    exact Finset.sum_congr rfl fun e _ => htr _ (P.coeff e).2 e

  haveI : IsReduced R := ⟨fun x hx => by
    have h1 : IsNilpotent (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k) := hx.map R.val
    have hs1 := hRss x x.2
    have e1 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 = 0 := by
      have hn1 := (h1.map (RingHom.fst (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn1 (by exact hs1.1)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    have e2 : (x : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 = 0 := by
      have hn2 := (h1.map (RingHom.snd (Matrix (Fin n) (Fin n) k) (Matrix (Fin n) (Fin n) k))).map
        (Matrix.toLinAlgEquiv' (R := k) (n := Fin n))
      have := Module.End.eq_zero_of_isNilpotent_isSemisimple hn2 (by exact hs1.2)
      exact (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).injective (this.trans (map_zero _).symm)
    exact Subtype.ext (Prod.ext e1 e2)⟩
  let ρ : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.fst k _ _).comp R.val)
  let ρ' : R →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toAlgHom.comp ((AlgHom.snd k _ _).comp R.val)
  have hρ : ∀ r : R, ρ r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).1 :=
    fun r => rfl
  have hρ' : ∀ r : R, ρ' r = Matrix.toLin' (r : Matrix (Fin n) (Fin n) k × Matrix (Fin n) (Fin n) k).2 :=
    fun r => rfl
  have htrace : ∀ r, LinearMap.trace k _ (ρ r) = LinearMap.trace k _ (ρ' r) := by
    intro r
    rw [hρ, hρ', Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq]
    obtain ⟨P, hP⟩ := hform r r.2
    rw [hP]
    exact htrP P
  obtain ⟨φ, hφ⟩ := hiso n R ρ ρ' htrace

  let A : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ : (Fin n → k) →ₗ[k] (Fin n → k))
  let B : Matrix (Fin n) (Fin n) k := LinearMap.toMatrix' (φ.symm : (Fin n → k) →ₗ[k] (Fin n → k))
  have hAB : A * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  have hBA : B * A = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext v : 1
    simp
  let g : GL (Fin n) k := ⟨A, B, hAB, hBA⟩

  have hint : ∀ x ∈ R, A * x.1 = x.2 * A := by
    intro x hx
    have hc : (φ : (Fin n → k) →ₗ[k] (Fin n → k)).comp (Matrix.toLin' x.1) =
        (Matrix.toLin' x.2).comp (φ : (Fin n → k) →ₗ[k] (Fin n → k)) := by
      refine LinearMap.ext fun v => ?_
      have := hφ ⟨x, hx⟩ v
      rw [hρ, hρ'] at this
      simpa using this
    have := congrArg LinearMap.toMatrix' hc
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin',
      LinearMap.toMatrix'_toLin'] at this
    exact this
  refine ⟨g, fun a ha => ?_, ?_⟩
  · have := hint (a, a) (Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩))
    exact this.symm
  · have h1 := hint (s, s') (Algebra.subset_adjoin (Or.inr rfl))
    show A * s * B = s'
    rw [h1, Matrix.mul_assoc, hAB, Matrix.mul_one]

end PositivityTheory.RgUd.T.Alg.Conj2
