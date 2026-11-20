import Formalism.LocalToGlobal.Columns.RecLevelLoc

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV (Pl kP St redAt redFn resS)
open Formalism.UG Formalism.UG.P

section Princ

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG : Finset (Pl E)) (H : Subgroup (GLG E n SG))

/- English proof (translation)
Unfold `rll_put`. Rewrite using `[afsplitU_coe, afsplitC_apply, Units.val_one]`. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, map_sub]`. Establish `he : afsplitEps E v = afsplitIE v (1 : E ⊗[F] v.adicCompletion F)` using `rfl`.

Rewrite using `[he]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.one_apply_ne hij, mul_zero, add_zero, sub_zero]`.
-/
theorem rll_put_entry (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (i j : Fin n) :
    (rll_put n v g : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j - (1 : Matrix (Fin n) (Fin n) _) i j =
      afsplitIE v ((g : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) _) i j) := by
  unfold rll_put
  rw [afsplitU_coe, afsplitC_apply, Units.val_one]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, mul_one, map_sub]
    have he : afsplitEps E v = afsplitIE v (1 : E ⊗[F] v.adicCompletion F) := rfl
    rw [he]
    ring
  · simp only [Matrix.one_apply_ne hij, mul_zero, add_zero, sub_zero]

/- English proof (translation)
Establish `hm : (Pi.single j 1 : Fin n → E) ∈ stdLat E n`. Rewrite using `[stdLat, Submodule.mem_pi]`. Introduce `i _`. Rewrite using `[Submodule.mem_one]`. Break down `eq_or_ne i j with rfl | hij` into its components or cases.

Conclude with `⟨1, by rw [Pi.single_eq_same, map_one]⟩`. Conclude with `⟨0, by rw [Pi.single_eq_of_ne hij, map_zero]⟩`. Use `show _ ∈ Submodule.span _ _`. Use `Submodule.subset_span ⟨Pi.single j 1, hm, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Break down `eq_or_ne i j with rfl | hij` into its components or cases. Simplify using `only [Pi.single_eq_same, map_one]`. Simplify using `only [Pi.single_eq_of_ne hij, map_zero]`.
-/
theorem rll_single_mem_std (v : HeightOneSpectrum (𝓞 F)) (j : Fin n) :
    (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (stdLat E n) := by
  have hm : (Pi.single j 1 : Fin n → E) ∈ stdLat E n := by
    rw [stdLat, Submodule.mem_pi]
    intro i _
    rw [Submodule.mem_one]
    rcases eq_or_ne i j with rfl | hij
    · exact ⟨1, by rw [Pi.single_eq_same, map_one]⟩
    · exact ⟨0, by rw [Pi.single_eq_of_ne hij, map_zero]⟩
  show _ ∈ Submodule.span _ _
  refine Submodule.subset_span ⟨Pi.single j 1, hm, ?_⟩
  funext i
  rcases eq_or_ne i j with rfl | hij
  · simp only [Pi.single_eq_same, map_one]
  · simp only [Pi.single_eq_of_ne hij, map_zero]

/- English proof (translation)
Establish `hU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F)` using `(Subgroup.mem_inf.mp hx).1`. Establish `hbase : Formalism.L2.Herm.locL v (baseLb E n ST) = Formalism.L2.Herm.locL v (stdLat E n)` using `rll_locL_base (n := n) (ST := ST) v hT`. Establish `hstab : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n))`. Rewrite using `[← hbase]`. Conclude with `(Subgroup.mem_inf.mp hx).2`.

Establish `hS : rll_put n v x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))` using `rll_put_mem_St (n := n) v hstab`. Establish `hUA : rll_put n v x ∈ UAd hc n` using `rll_put_mem_UAd (hc := hc) (n := n) v hU`. Establish `hJ : rll_put n v x ∈ J0 hc n ST`. Rewrite using `[mem_mirabolicLevel_iff_reduction]`. Use `⟨hUA, hS, fun P hP => ?_⟩` and prove the remaining obligations.

Rewrite using `[rll_put_red (n := n) v x hS P (fun hv => hT ⟨P, hP, hv⟩)]`. Conclude with `one_mem _`. Establish `hred : redG hc n ST SG ⟨rll_put n v x, hJ⟩ = 1`. Use function extensionality and compare the values at `w`. Use `show redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨rll_put n v x, hS⟩ = 1`.

Distinguish the cases in `hw : IsOver v w.1`. Use `set k := Formalism.L2.DIV.pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨rll_put n v x, hS⟩ with hkdef`. Establish `hk : ∀ i j, (((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (rll_put n v x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j`. Introduce `i j`. Establish `e` using `congrArg (fun y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) => (y.val : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j) (Formalism.L2.DIV.frGL_pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨rll_put n v x, hS⟩)`.

Simplify `e` using `[Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, bc, MulAut.conj_apply, ← hkdef]`. Establish `h1ij : ∀ i j, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j`. Introduce `i j`. Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq]`.

Both sides reduce to the same expression. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]`. Both sides reduce to the same expression. Establish `hgS : ((g : Formalism.L2.Herm.intAf F E)) ∈ Formalism.L2.DIV.idS F w.1.asIdeal`. Establish `e : ((g : Formalism.L2.Herm.intAf F E)) = Formalism.L2.DIV.oToS F E (g : 𝓞 E)` using `by rw [map_natCast]`.

Rewrite using `[e]`. Conclude with `Ideal.mem_map_of_mem _ (hg w.1 w.2 hw)`. Establish `hmem : ∀ i j, (k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j ∈ Formalism.L2.DIV.idS F w.1.asIdeal`. Introduce `i j`. Establish `hy : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (baseLb E n ST)`.

Rewrite using `[hbase]`. Conclude with `rll_single_mem_std n v j`. Take `⟨z, hz, hxz⟩` from `hp _ hy`. Rewrite `hz` using `[hbase, rll_locL_std, Formalism.UG.stdLat, Submodule.mem_pi]`. Take `⟨s, hs⟩` from `hz i (Set.mem_univ i)`.

Establish `hzi : z i = (s : E ⊗[F] v.adicCompletion F)` using `hs.symm`. Establish `hmv` using `congrFun hxz i`. Establish `hxij : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j = (g : E ⊗[F] v.adicCompletion F) * (s : E ⊗[F] v.adicCompletion F)`. Rewrite using `[← hzi]`. Simplify `hmv` using `[Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]`.

Establish `hint` using `afsplit_IE_int v (s : E ⊗[F] v.adicCompletion F) s.2`. Establish `e : (k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j - (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j = (g : Formalism.L2.Herm.intAf F E) * ⟨_, hint⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show (((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) - (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = _`. Rewrite using `[hk, h1ij, rll_put_entry, hxij, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ hgS`. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `i j`. Use `show Formalism.L2.DIV.resS F w.1 ((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j) = (1 : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP w.1)) i j`. Establish `h0` using `(Formalism.L2.DIV.resS_eq_zero_iff w.1 _).mpr (hmem i j)`. Rewrite `h0` using `[map_sub, sub_eq_zero]`. Rewrite using `[h0]`.

Break down `eq_or_ne i j with rfl | hij` into its components or cases. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]`. Conclude with `rll_put_red (n := n) v x hS w.1 hw`. Use `Subgroup.mem_map.mpr ⟨rll_put n v x, (mem_levU hc n ST SG H).mpr ⟨hJ, ?_⟩, rll_put_self (n := n) v x⟩` and prove the remaining obligations.

Rewrite using `[hred]`. Conclude with `one_mem H`.
-/
theorem levLoc_of_princ (v : HeightOneSpectrum (𝓞 F)) (g : ℕ) (hT : v ∉ plUnder F ST)
    (hg : ∀ w ∈ SG, IsOver v w → (g : 𝓞 E) ∈ w.asIdeal) (x : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (hx : x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST))
    (hp : ∀ y ∈ Formalism.L2.Herm.locL v (baseLb E n ST), ∃ z ∈ Formalism.L2.Herm.locL v (baseLb E n ST),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (g : E ⊗[F] v.adicCompletion F) • z) :
    x ∈ levLoc hc n ST SG H v := by
  have hU : x ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) := (Subgroup.mem_inf.mp hx).1
  have hbase : Formalism.L2.Herm.locL v (baseLb E n ST) = Formalism.L2.Herm.locL v (stdLat E n) :=
    rll_locL_base (n := n) (ST := ST) v hT
  have hstab : x ∈ stabGL (Formalism.L2.Herm.locL v (stdLat E n)) := by
    rw [← hbase]
    exact (Subgroup.mem_inf.mp hx).2
  have hS : rll_put n v x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :=
    rll_put_mem_St (n := n) v hstab
  have hUA : rll_put n v x ∈ UAd hc n := rll_put_mem_UAd (hc := hc) (n := n) v hU
  have hJ : rll_put n v x ∈ J0 hc n ST := by
    rw [mem_mirabolicLevel_iff_reduction]
    refine ⟨hUA, hS, fun P hP => ?_⟩
    rw [rll_put_red (n := n) v x hS P (fun hv => hT ⟨P, hP, hv⟩)]
    exact one_mem _
  have hred : redG hc n ST SG ⟨rll_put n v x, hJ⟩ = 1 := by
    funext w
    show redAt (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ⟨rll_put n v x, hS⟩ = 1
    by_cases hw : IsOver v w.1
    · set k := Formalism.L2.DIV.pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨rll_put n v x, hS⟩ with hkdef
      have hk : ∀ i j, (((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
          E ⊗[F] Formalism.L2.Herm.Af F) = (rll_put n v x : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j := by
        intro i j
        have e := congrArg (fun y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) =>
          (y.val : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j)
          (Formalism.L2.DIV.frGL_pullFr (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ⟨rll_put n v x, hS⟩)
        simpa [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, bc, MulAut.conj_apply, ← hkdef] using e
      have h1ij : ∀ i j, (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
          E ⊗[F] Formalism.L2.Herm.Af F) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) i j := by
        intro i j
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, Matrix.one_apply_eq]; rfl
        · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij]; rfl
      have hgS : ((g : Formalism.L2.Herm.intAf F E)) ∈ Formalism.L2.DIV.idS F w.1.asIdeal := by
        have e : ((g : Formalism.L2.Herm.intAf F E)) = Formalism.L2.DIV.oToS F E (g : 𝓞 E) := by rw [map_natCast]
        rw [e]
        exact Ideal.mem_map_of_mem _ (hg w.1 w.2 hw)
      have hmem : ∀ i j, (k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j -
          (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j ∈ Formalism.L2.DIV.idS F w.1.asIdeal := by
        intro i j
        have hy : (Pi.single j 1 : Fin n → E ⊗[F] v.adicCompletion F) ∈ Formalism.L2.Herm.locL v (baseLb E n ST) := by
          rw [hbase]; exact rll_single_mem_std n v j
        obtain ⟨z, hz, hxz⟩ := hp _ hy
        rw [hbase, rll_locL_std, Formalism.UG.stdLat, Submodule.mem_pi] at hz
        obtain ⟨s, hs⟩ := hz i (Set.mem_univ i)
        have hzi : z i = (s : E ⊗[F] v.adicCompletion F) := hs.symm
        have hmv := congrFun hxz i
        have hxij : (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j -
            (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j =
            (g : E ⊗[F] v.adicCompletion F) * (s : E ⊗[F] v.adicCompletion F) := by
          rw [← hzi]
          simpa [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.one_apply] using hmv
        have hint := afsplit_IE_int v (s : E ⊗[F] v.adicCompletion F) s.2
        have e : (k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j -
            (1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j =
            (g : Formalism.L2.Herm.intAf F E) * ⟨_, hint⟩ := by
          apply Subtype.ext
          show (((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j : Formalism.L2.Herm.intAf F E) :
              E ⊗[F] Formalism.L2.Herm.Af F) - (((1 : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j :
              Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) = _
          rw [hk, h1ij, rll_put_entry, hxij, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
          push_cast
          rfl
        rw [e]
        exact Ideal.mul_mem_right _ _ hgS
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS F w.1 ((k : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j) =
        (1 : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP w.1)) i j
      have h0 := (Formalism.L2.DIV.resS_eq_zero_iff w.1 _).mpr (hmem i j)
      rw [map_sub, sub_eq_zero] at h0
      rw [h0]
      rcases eq_or_ne i j with rfl | hij
      · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
    · exact rll_put_red (n := n) v x hS w.1 hw
  refine Subgroup.mem_map.mpr ⟨rll_put n v x, (mem_levU hc n ST SG H).mpr ⟨hJ, ?_⟩, rll_put_self (n := n) v x⟩
  rw [hred]
  exact one_mem H

end Princ

section DLat

variable {E : Type} [Field E] [NumberField E] (n : ℕ) [NeZero n]

def rll_dLat (c : E) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | (∀ i, i ≠ lastIdx n → x i ∈ intOE E) ∧ c * x (lastIdx n) ∈ intOE E}
  zero_mem' := ⟨fun _ _ => zero_mem _, by rw [Pi.zero_apply, mul_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨fun i hi => add_mem (ha.1 i hi) (hb.1 i hi), by
    rw [Pi.add_apply, mul_add]; exact add_mem ha.2 hb.2⟩
  smul_mem' := fun s a ha => ⟨fun i hi => by
    rw [Pi.smul_apply, Algebra.smul_def]; exact mul_mem ⟨s, rfl⟩ (ha.1 i hi), by
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]; exact mul_mem ⟨s, rfl⟩ ha.2⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem rll_mem_dLat (c : E) (x : Fin n → E) :
    x ∈ rll_dLat n c ↔ (∀ i, i ≠ lastIdx n → x i ∈ intOE E) ∧ c * x (lastIdx n) ∈ intOE E := Iff.rfl

variable {F : Type} [Field F] [NumberField F] [Algebra F E]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [Pi.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem rll_single_inclV (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (e : E) :
    (fun j => inclE (F := F) (v.adicCompletion F) ((Pi.single i e : Fin n → E) j)) =
      Pi.single i (inclE (F := F) (v.adicCompletion F) e) := by
  funext j
  simp only [Pi.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hO : ∀ e ∈ intOE E, inclE (F` using `F) (v.adicCompletion F) e ∈ Formalism.BasicNotions.intV E v := by`. Introduce `e he`. Use `show _ ∈ Subring.closure _`. Conclude with `Subring.subset_closure (Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩)`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (Formalism.BasicNotions.intV E v) ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) '' (rll_dLat n c : Set (Fin n → E))) at hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨x, hx, rfl⟩` from `hx`.

Rewrite `hx` using `[SetLike.mem_coe, rll_mem_dLat]`. Use `⟨fun i hi => hO _ (hx.1 i hi), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Conclude with `hO _ hx.2`. Consider the case `zero`.

Use `⟨fun i _ => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.zero_apply]`. Conclude with `zero_mem _`. Rewrite using `[Pi.zero_apply, mul_zero]`. Conclude with `zero_mem _`.

Consider the case `add x y _ _ hx hy`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.add_apply]`. Conclude with `add_mem (hx.1 i hi) (hy.1 i hi)`. Rewrite using `[Pi.add_apply, mul_add]`.

Conclude with `add_mem hx.2 hy.2`. Consider the case `smul s x _ hx`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul]`. Conclude with `mul_mem s.2 (hx.1 i hi)`.

Rewrite using `[Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]`. Conclude with `mul_mem s.2 hx.2`. Introduce and unpack `⟨h1, h2⟩`. Express the relevant statement in the definitionally equal form `z ∈ Submodule.span (Formalism.BasicNotions.intV E v) ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) '' (rll_dLat n c : Set (Fin n → E)))`. Establish `hz : z = ∑ i, Pi.single i (z i)` using `by first`.

Consider the case `exact (Finset.univ_sum_single z).symm`. Consider the case `(funext j; simp [Finset.sum_apply, Pi.single_apply])`. Rewrite using `[hz]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hgen : ∀ e : E, (Pi.single i e : Fin n → E) ∈ rll_dLat n c → (Pi.single i (inclE (F` using `F) (v.adicCompletion F) e) : Fin n → E ⊗[F] v.adicCompletion F) ∈ Submodule.span (Formalism.BasicNotions.intV E v) ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) '' (rll_dLat n c : Set (Fin n → E))) := by`.

Introduce `e he`. Rewrite using `[← rll_single_inclV]`. Conclude with `Submodule.subset_span ⟨_, he, rfl⟩`. Distinguish the cases in `hi : i = lastIdx n`. Substitute `hi` using the available equality.

Establish `e1 : (Pi.single (lastIdx n) (z (lastIdx n)) : Fin n → E ⊗[F] v.adicCompletion F) = (⟨_, h2⟩ : Formalism.BasicNotions.intV E v) • Pi.single (lastIdx n) (inclE (F` using `F) (v.adicCompletion F) c⁻¹) := by`. Use function extensionality and compare the values at `j`. Break down `eq_or_ne j (lastIdx n) with rfl | hj` into its components or cases. Rewrite using `[Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Subring.smul_def, smul_eq_mul] show _ = (inclE (F := F) (v.adicCompletion F) c * z (lastIdx n)) * inclE (F := F) (v.adicCompletion F) c⁻¹`. Rewrite using `[mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]`.

Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]`. Rewrite using `[e1]`. Use `Submodule.smul_mem _ _ (hgen _ ?_)` and prove the remaining obligations. Rewrite using `[rll_mem_dLat]`. Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_same, mul_inv_cancel₀ hc0]`. Conclude with `one_mem _`. Establish `e2 : (Pi.single i (z i) : Fin n → E ⊗[F] v.adicCompletion F) = (⟨_, h1 i hi⟩ : Formalism.BasicNotions.intV E v) • Pi.single i (inclE (F` using `F) (v.adicCompletion F) 1) := by`.

Use function extensionality and compare the values at `j`. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Rewrite using `[Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Subring.smul_def, smul_eq_mul, map_one, mul_one]`. Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]`. Rewrite using `[e2]`.

Use `Submodule.smul_mem _ _ (hgen _ ?_)` and prove the remaining obligations. Rewrite using `[rll_mem_dLat]`. Use `⟨fun j _ => ?_, ?_⟩` and prove the remaining obligations. Break down `eq_or_ne j i with rfl | hj` into its components or cases. Rewrite using `[Pi.single_eq_same]`.

Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_of_ne (fun e => hi e.symm), mul_zero]`. Conclude with `zero_mem _`.
-/
theorem rll_mem_loc_dLat (v : HeightOneSpectrum (𝓞 F)) (c : E) (hc0 : c ≠ 0) (z : Fin n → E ⊗[F] v.adicCompletion F) :
    z ∈ Formalism.L2.Herm.locL v (rll_dLat n c) ↔ (∀ i, i ≠ lastIdx n → z i ∈ Formalism.BasicNotions.intV E v) ∧
      inclE (F := F) (v.adicCompletion F) c * z (lastIdx n) ∈ Formalism.BasicNotions.intV E v := by
  have hO : ∀ e ∈ intOE E, inclE (F := F) (v.adicCompletion F) e ∈ Formalism.BasicNotions.intV E v := by
    intro e he
    show _ ∈ Subring.closure _
    exact Subring.subset_closure (Set.mem_union_left _ ⟨⟨e, he⟩, rfl⟩)
  constructor
  · intro hz
    change z ∈ Submodule.span (Formalism.BasicNotions.intV E v)
      ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) ''
        (rll_dLat n c : Set (Fin n → E))) at hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, rll_mem_dLat] at hx
      refine ⟨fun i hi => hO _ (hx.1 i hi), ?_⟩
      rw [← map_mul]
      exact hO _ hx.2
    | zero =>
      refine ⟨fun i _ => ?_, ?_⟩
      · rw [Pi.zero_apply]; exact zero_mem _
      · rw [Pi.zero_apply, mul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.add_apply]; exact add_mem (hx.1 i hi) (hy.1 i hi)
      · rw [Pi.add_apply, mul_add]; exact add_mem hx.2 hy.2
    | smul s x _ hx =>
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; exact mul_mem s.2 (hx.1 i hi)
      · rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]; exact mul_mem s.2 hx.2
  · rintro ⟨h1, h2⟩
    change z ∈ Submodule.span (Formalism.BasicNotions.intV E v)
      ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) ''
        (rll_dLat n c : Set (Fin n → E)))
    have hz : z = ∑ i, Pi.single i (z i) := by
      first
        | exact (Finset.univ_sum_single z).symm
        | (funext j; simp [Finset.sum_apply, Pi.single_apply])
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hgen : ∀ e : E, (Pi.single i e : Fin n → E) ∈ rll_dLat n c →
        (Pi.single i (inclE (F := F) (v.adicCompletion F) e) : Fin n → E ⊗[F] v.adicCompletion F) ∈
          Submodule.span (Formalism.BasicNotions.intV E v)
            ((fun x : Fin n → E => fun i => inclE (F := F) (v.adicCompletion F) (x i)) ''
              (rll_dLat n c : Set (Fin n → E))) := by
      intro e he
      rw [← rll_single_inclV]
      exact Submodule.subset_span ⟨_, he, rfl⟩
    by_cases hi : i = lastIdx n
    · subst hi
      have e1 : (Pi.single (lastIdx n) (z (lastIdx n)) : Fin n → E ⊗[F] v.adicCompletion F) =
          (⟨_, h2⟩ : Formalism.BasicNotions.intV E v) • Pi.single (lastIdx n) (inclE (F := F) (v.adicCompletion F) c⁻¹) := by
        funext j
        rcases eq_or_ne j (lastIdx n) with rfl | hj
        · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Subring.smul_def, smul_eq_mul]
          show _ = (inclE (F := F) (v.adicCompletion F) c * z (lastIdx n)) * inclE (F := F) (v.adicCompletion F) c⁻¹
          rw [mul_comm, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      rw [e1]
      refine Submodule.smul_mem _ _ (hgen _ ?_)
      rw [rll_mem_dLat]
      refine ⟨fun j hj => ?_, ?_⟩
      · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
      · rw [Pi.single_eq_same, mul_inv_cancel₀ hc0]; exact one_mem _
    · have e2 : (Pi.single i (z i) : Fin n → E ⊗[F] v.adicCompletion F) =
          (⟨_, h1 i hi⟩ : Formalism.BasicNotions.intV E v) • Pi.single i (inclE (F := F) (v.adicCompletion F) 1) := by
        funext j
        rcases eq_or_ne j i with rfl | hj
        · rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Subring.smul_def, smul_eq_mul,
            map_one, mul_one]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      rw [e2]
      refine Submodule.smul_mem _ _ (hgen _ ?_)
      rw [rll_mem_dLat]
      refine ⟨fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
      · rw [Pi.single_eq_of_ne (fun e => hi e.symm), mul_zero]; exact zero_mem _

end DLat

section Pi

variable {E : Type} [Field E] [NumberField E] [StarRing E] (n : ℕ) [NeZero n] (ST : Finset (Pl E))

structure BasePi (π : 𝓞 E) : Prop where
  dvd : ∀ r : 𝓞 E, (∀ P ∈ ST, r ∈ P.asIdeal) ↔ π ∣ r
  cop : IsCoprime π (cO E π)

variable {ST} {π : 𝓞 E}

/- English proof (translation)
Introduce `h0`. Establish `hc` using `h.cop`. Rewrite `hc` using `[h0, map_zero]`. Conclude with `not_isCoprime_zero_zero hc`.
-/
theorem BasePi.ne_zero (h : BasePi ST π) : π ≠ 0 := by
  intro h0
  have hc := h.cop
  rw [h0, map_zero] at hc
  exact not_isCoprime_zero_zero hc

/- English proof (translation)
Introduce `h0`. Apply `h.ne_zero` to reduce the goal to its premises. Use `first`. Consider the case `exact (injective_iff_map_eq_zero _).mp (FaithfulSMul.algebraMap_injective (𝓞 E) E) _ h0`. Consider the case `exact RingOfIntegers.coe_eq_zero_iff.mp h0`.
-/
theorem BasePi.coe_ne_zero (h : BasePi ST π) : algebraMap (𝓞 E) E π ≠ 0 := by
  intro h0
  apply h.ne_zero
  first
    | exact (injective_iff_map_eq_zero _).mp (FaithfulSMul.algebraMap_injective (𝓞 E) E) _ h0
    | exact RingOfIntegers.coe_eq_zero_iff.mp h0

/- English proof (translation)
The claim follows from `_root_.star_ne_zero.mpr h.coe_ne_zero`.
-/
theorem BasePi.star_ne_zero (h : BasePi ST π) : star (algebraMap (𝓞 E) E π) ≠ 0 := _root_.star_ne_zero.mpr h.coe_ne_zero

/- English proof (translation)
The claim follows from `(h.dvd π).mpr dvd_rfl P hP`.
-/
theorem BasePi.mem (h : BasePi ST π) {P : Pl E} (hP : P ∈ ST) : π ∈ P.asIdeal := (h.dvd π).mpr dvd_rfl P hP

/- English proof (translation)
Introduce `hc`. Take `⟨a, b, hab⟩` from `h.cop`. Apply `P.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `add_mem (Ideal.mul_mem_left _ _ (h.mem hP)) (Ideal.mul_mem_left _ _ hc)`.
-/
theorem BasePi.conj_notMem (h : BasePi ST π) {P : Pl E} (hP : P ∈ ST) : cO E π ∉ P.asIdeal := by
  intro hc
  obtain ⟨a, b, hab⟩ := h.cop
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact add_mem (Ideal.mul_mem_left _ _ (h.mem hP)) (Ideal.mul_mem_left _ _ hc)

/- English proof (translation)
Establish `hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a` using `fun a => Iff.rfl`. Use extensionality with `x`. Rewrite using `[rll_mem_baseLb, rll_mem_dLat]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr, hP⟩`.

Use `⟨fun i _ => (hI _).mpr ⟨r i, hr i⟩, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `(h.dvd _).mp hP`. Use `(hI _).mpr ⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr (lastIdx n), ht, map_mul, inv_mul_cancel_left₀ h.coe_ne_zero]`. Introduce and unpack `⟨h1, h2⟩`.

Take `⟨t, ht⟩` from `(hI _).mp h2`. Use `⟨fun i => if hi : i = lastIdx n then π * t else ((hI _).mp (h1 i hi)).choose, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Distinguish the cases in `hi : i = lastIdx n`. Substitute `hi dsimp only` using the available equality.

Rewrite using `[dif_pos rfl, map_mul, ht, mul_inv_cancel_left₀ h.coe_ne_zero]`. Simplify using `only [dif_neg hi]`. Conclude with `((hI _).mp (h1 i hi)).choose_spec`. Introduce `P hP dsimp only`. Rewrite using `[dif_pos rfl]`.

Conclude with `Ideal.mul_mem_right _ _ (h.mem hP)`.
-/
theorem rll_baseLb_eq (h : BasePi ST π) : baseLb E n ST = rll_dLat n (algebraMap (𝓞 E) E π)⁻¹ := by
  have hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := fun a => Iff.rfl
  ext x
  rw [rll_mem_baseLb, rll_mem_dLat]
  constructor
  · rintro ⟨r, hr, hP⟩
    refine ⟨fun i _ => (hI _).mpr ⟨r i, hr i⟩, ?_⟩
    obtain ⟨t, ht⟩ := (h.dvd _).mp hP
    refine (hI _).mpr ⟨t, ?_⟩
    rw [← hr (lastIdx n), ht, map_mul, inv_mul_cancel_left₀ h.coe_ne_zero]
  · rintro ⟨h1, h2⟩
    obtain ⟨t, ht⟩ := (hI _).mp h2
    classical
    refine ⟨fun i => if hi : i = lastIdx n then π * t else ((hI _).mp (h1 i hi)).choose, ?_, ?_⟩
    · intro i
      by_cases hi : i = lastIdx n
      · subst hi
        dsimp only
        rw [dif_pos rfl, map_mul, ht, mul_inv_cancel_left₀ h.coe_ne_zero]
      · simp only [dif_neg hi]
        exact ((hI _).mp (h1 i hi)).choose_spec
    · intro P hP
      dsimp only
      rw [dif_pos rfl]
      exact Ideal.mul_mem_right _ _ (h.mem hP)

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, Submodule.mem_one]`. Both sides reduce to the same expression.
-/
theorem rll_one_eq_range : ((1 : Submodule (𝓞 E) E) : Set E) = (intOE E : Set E) := by
  ext x
  simp only [SetLike.mem_coe, Submodule.mem_one]
  rfl

/- English proof (translation)
Take `⟨r, rfl⟩` from `ha`. Conclude with `⟨cO E r, rfl⟩`.
-/
theorem rll_star_mem {a : E} (ha : a ∈ intOE E) : star a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨cO E r, rfl⟩

/- English proof (translation)
Establish `hH : ∀ x y : Fin n → E, hStd E n x y = ∑ i, star (x i) * y i` using `fun _ _ => rfl`. Establish `hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a` using `fun a => Iff.rfl`. Establish `hs` using `h.star_ne_zero`. Establish `hsingle : ∀ (i : Fin n) (e : E), (Pi.single i e : Fin n → E) ∈ baseLb E n ST → hStd E n (Pi.single i e) y = star e * y i`. Introduce `i e _`.

Rewrite using `[hH, Finset.sum_eq_single i]`. Rewrite using `[Pi.single_eq_same]`. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj, star_zero, zero_mul]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`. Rewrite using `[rll_mem_dLat]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Prove the components needed by the constructor for the conclusion.

Introduce `i hi`. Establish `hm : (Pi.single i 1 : Fin n → E) ∈ baseLb E n ST`. Rewrite using `[rll_baseLb_eq n h, rll_mem_dLat]`. Use `⟨fun j _ => ?_, ?_⟩` and prove the remaining obligations. Break down `eq_or_ne j i with rfl | hj` into its components or cases.

Rewrite using `[Pi.single_eq_same]`. Conclude with `one_mem _`. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_of_ne (fun e => hi e.symm), mul_zero]`.

Conclude with `zero_mem _`. Use `H _ hm` as an intermediate fact. Rewrite `this` using `[hsingle i 1 hm, star_one, one_mul]`. Then use the resulting hypothesis. Establish `hm : (Pi.single (lastIdx n) (algebraMap (𝓞 E) E π) : Fin n → E) ∈ baseLb E n ST`. Rewrite using `[rll_baseLb_eq n h, rll_mem_dLat]`.

Use `⟨fun j hj => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Pi.single_eq_of_ne hj]`. Conclude with `zero_mem _`. Rewrite using `[Pi.single_eq_same, inv_mul_cancel₀ h.coe_ne_zero]`. Conclude with `one_mem _`.

Use `H _ hm` as an intermediate fact. Rewrite `this` using `[hsingle _ _ hm]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2⟩ x hx`. Rewrite `hx` using `[rll_baseLb_eq n h, rll_mem_dLat]`. Rewrite using `[hH]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = lastIdx n`. Substitute `hi` using the available equality. Establish `e : star (x (lastIdx n)) * y (lastIdx n) = star ((algebraMap (𝓞 E) E π)⁻¹ * x (lastIdx n)) * (star (algebraMap (𝓞 E) E π) * y (lastIdx n))`. Rewrite using `[star_mul', star_inv₀, mul_mul_mul_comm, inv_mul_cancel₀ hs, one_mul]`.

Rewrite using `[e]`. Conclude with `mul_mem (rll_star_mem hx.2) h2`. Conclude with `mul_mem (rll_star_mem (hx.1 i hi)) (h1 i hi)`.
-/
theorem rll_dual_iff (h : BasePi ST π) (y : Fin n → E) :
    (∀ x ∈ baseLb E n ST, hStd E n x y ∈ intOE E) ↔ y ∈ rll_dLat n (star (algebraMap (𝓞 E) E π)) := by
  have hH : ∀ x y : Fin n → E, hStd E n x y = ∑ i, star (x i) * y i := fun _ _ => rfl
  have hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := fun a => Iff.rfl
  have hs := h.star_ne_zero
  have hsingle : ∀ (i : Fin n) (e : E), (Pi.single i e : Fin n → E) ∈ baseLb E n ST →
      hStd E n (Pi.single i e) y = star e * y i := by
    intro i e _
    rw [hH, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j _ hj
      rw [Pi.single_eq_of_ne hj, star_zero, zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [rll_mem_dLat]
  constructor
  · intro H
    constructor
    · intro i hi
      have hm : (Pi.single i 1 : Fin n → E) ∈ baseLb E n ST := by
        rw [rll_baseLb_eq n h, rll_mem_dLat]
        refine ⟨fun j _ => ?_, ?_⟩
        · rcases eq_or_ne j i with rfl | hj
          · rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
        · rw [Pi.single_eq_of_ne (fun e => hi e.symm), mul_zero]; exact zero_mem _
      have := H _ hm
      rwa [hsingle i 1 hm, star_one, one_mul] at this
    · have hm : (Pi.single (lastIdx n) (algebraMap (𝓞 E) E π) : Fin n → E) ∈ baseLb E n ST := by
        rw [rll_baseLb_eq n h, rll_mem_dLat]
        refine ⟨fun j hj => ?_, ?_⟩
        · rw [Pi.single_eq_of_ne hj]; exact zero_mem _
        · rw [Pi.single_eq_same, inv_mul_cancel₀ h.coe_ne_zero]; exact one_mem _
      have := H _ hm
      rwa [hsingle _ _ hm] at this
  · rintro ⟨h1, h2⟩ x hx
    rw [rll_baseLb_eq n h, rll_mem_dLat] at hx
    rw [hH]
    refine sum_mem fun i _ => ?_
    by_cases hi : i = lastIdx n
    · subst hi
      have e : star (x (lastIdx n)) * y (lastIdx n) =
          star ((algebraMap (𝓞 E) E π)⁻¹ * x (lastIdx n)) * (star (algebraMap (𝓞 E) E π) * y (lastIdx n)) := by
        rw [star_mul', star_inv₀, mul_mul_mul_comm, inv_mul_cancel₀ hs, one_mul]
      rw [e]
      exact mul_mem (rll_star_mem hx.2) h2
    · exact mul_mem (rll_star_mem (hx.1 i hi)) (h1 i hi)

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[← rll_dual_iff n h y]`. Use `show y ∈ Formalism.E.hdual (hStd E n) (baseLb E n ST) ↔ _`. Simplify using `only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[← SetLike.mem_coe, rll_one_eq_range, SetLike.mem_coe]`.
-/
theorem rll_baseSh_eq (h : BasePi ST π) : baseSh E n ST = rll_dLat n (star (algebraMap (𝓞 E) E π)) := by
  ext y
  rw [← rll_dual_iff n h y]
  show y ∈ Formalism.E.hdual (hStd E n) (baseLb E n ST) ↔ _
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  refine forall₂_congr fun x _ => ?_
  rw [← SetLike.mem_coe, rll_one_eq_range, SetLike.mem_coe]

end Pi

section Pi2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
variable (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST : Finset (Pl E)} {π : 𝓞 E}

/- English proof (translation)
Establish `hform_eq : ∀ x y : Fin n → E, Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y`. Introduce `x y`. Use `show _ = ∑ i, star (x i) * y i`. Simplify using `only [Formalism.UG.hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Both sides reduce to the same expression.

Establish `hset : Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) = (rll_dLat n (star (algebraMap (𝓞 E) E π)) : Set (Fin n → E))`. Use extensionality with `y`. Rewrite using `[SetLike.mem_coe, ← rll_dual_iff n h y]`. Use `show (∀ x ∈ baseLb E n ST, Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y ∈ (algebraMap (𝓞 E) E).range) ↔ _`. Use `forall₂_congr fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[hform_eq x y]`. Both sides reduce to the same expression. Use `show Submodule.span (𝓞 E) _ = _`. Rewrite using `[hset, Submodule.span_eq]`.
-/
theorem rll_baseDual_eq (h : BasePi ST π) : baseDual hc n ST = rll_dLat n (star (algebraMap (𝓞 E) E π)) := by
  have hform_eq : ∀ x y : Fin n → E,
      Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y = hStd E n x y := by
    intro x y
    show _ = ∑ i, star (x i) * y i
    simp only [Formalism.UG.hform, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  have hset : Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST) =
      (rll_dLat n (star (algebraMap (𝓞 E) E π)) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, ← rll_dual_iff n h y]
    show (∀ x ∈ baseLb E n ST, Formalism.UG.hform (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) x y ∈
      (algebraMap (𝓞 E) E).range) ↔ _
    refine forall₂_congr fun x _ => ?_
    rw [hform_eq x y]
    rfl
  show Submodule.span (𝓞 E) _ = _
  rw [hset, Submodule.span_eq]

/- English proof (translation)
Establish `hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a` using `fun a => Iff.rfl`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `by first`. Consider the case `exact FaithfulSMul.algebraMap_injective (𝓞 E) E`. Consider the case `exact RingOfIntegers.coe_injective`. Establish `ha` using `h.coe_ne_zero`.

Establish `hb : star (algebraMap (𝓞 E) E π) = algebraMap (𝓞 E) E (cO E π)` using `rfl`. Establish `hloc : ∀ (y : Fin n → E) (P : Pl E), y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST) ↔ ∃ s ∈ P.asIdeal.primeCompl, s • y ∈ baseLb E n ST` using `fun _ _ => Iff.rfl`. Use extensionality with `y`. Use `show y ∈ baseSh E n ST ⊓ ⨅ P ∈ ST, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST) ↔ _`. Rewrite using `[Submodule.mem_inf, rll_baseSh_eq n h, rll_mem_dLat, rll_mem_dLat]`.

Simplify using `only [Submodule.mem_iInf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `(hI _).mp h2`.

Establish `hrP : ∀ P ∈ ST, r ∈ P.asIdeal`. Introduce `P hP`. Take `⟨s, hs, hsy⟩` from `(hloc y P).mp (h3 P hP)`. Rewrite `hsy` using `[rll_baseLb_eq n h, rll_mem_dLat]`. Take `⟨t, ht⟩` from `(hI _).mp hsy.2`.

Establish `e : s * r = cO E π * π * t`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [map_mul]`. Rewrite using `[hr, ← hb, ht, Pi.smul_apply, Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Establish `hmem : s * r ∈ P.asIdeal`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (h.mem hP))`. Conclude with `(P.isPrime.mem_or_mem hmem).resolve_left (Ideal.mem_primeCompl_iff.mp hs)`.

Take `⟨q, hq⟩` from `(h.dvd r).mp hrP`. Use `(hI _).mpr ⟨q, ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[hq, map_mul]`. Rewrite using `[div_mul_eq_mul_div, ← hr]`. Clear the denominators using the available nonvanishing facts.

Apply the tactic sequence `try ring`. Introduce and unpack `⟨h1, h2⟩`. Take `⟨q, hq⟩` from `(hI _).mp h2`. Use `⟨⟨h1, ?_⟩, fun P hP => (hloc y P).mpr ⟨cO E π, Ideal.mem_primeCompl_iff.mpr (h.conj_notMem hP), ?_⟩⟩` and prove the remaining obligations. Use `(hI _).mpr ⟨π * q, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hq]`. Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`. Rewrite using `[rll_baseLb_eq n h, rll_mem_dLat]`. Use `⟨fun i hi => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Conclude with `mul_mem ⟨cO E π, rfl⟩ (h1 i hi)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, ← hb]`. Use `(hI _).mpr ⟨q, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`.

Clear the denominators using the available nonvanishing facts. Apply the tactic sequence `try ring`.
-/
theorem rll_baseKer_eq (h : BasePi ST π) :
    baseKer E n ST = rll_dLat n (star (algebraMap (𝓞 E) E π) / algebraMap (𝓞 E) E π) := by
  have hI : ∀ a : E, a ∈ intOE E ↔ ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = a := fun a => Iff.rfl
  have hinj : Function.Injective (algebraMap (𝓞 E) E) := by
    first
      | exact FaithfulSMul.algebraMap_injective (𝓞 E) E
      | exact RingOfIntegers.coe_injective
  have ha := h.coe_ne_zero
  have hb : star (algebraMap (𝓞 E) E π) = algebraMap (𝓞 E) E (cO E π) := rfl
  have hloc : ∀ (y : Fin n → E) (P : Pl E), y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST) ↔
      ∃ s ∈ P.asIdeal.primeCompl, s • y ∈ baseLb E n ST := fun _ _ => Iff.rfl
  ext y
  show y ∈ baseSh E n ST ⊓ ⨅ P ∈ ST, Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (baseLb E n ST) ↔ _
  rw [Submodule.mem_inf, rll_baseSh_eq n h, rll_mem_dLat, rll_mem_dLat]
  simp only [Submodule.mem_iInf]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_⟩
    obtain ⟨r, hr⟩ := (hI _).mp h2
    have hrP : ∀ P ∈ ST, r ∈ P.asIdeal := by
      intro P hP
      obtain ⟨s, hs, hsy⟩ := (hloc y P).mp (h3 P hP)
      rw [rll_baseLb_eq n h, rll_mem_dLat] at hsy
      obtain ⟨t, ht⟩ := (hI _).mp hsy.2
      have e : s * r = cO E π * π * t := by
        apply hinj
        simp only [map_mul]
        rw [hr, ← hb, ht, Pi.smul_apply, Algebra.smul_def]
        field_simp
        try ring
      have hmem : s * r ∈ P.asIdeal := by
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (h.mem hP))
      exact (P.isPrime.mem_or_mem hmem).resolve_left (Ideal.mem_primeCompl_iff.mp hs)
    obtain ⟨q, hq⟩ := (h.dvd r).mp hrP
    refine (hI _).mpr ⟨q, ?_⟩
    rw [hq, map_mul] at hr
    rw [div_mul_eq_mul_div, ← hr]
    field_simp
    try ring
  · rintro ⟨h1, h2⟩
    obtain ⟨q, hq⟩ := (hI _).mp h2
    refine ⟨⟨h1, ?_⟩, fun P hP => (hloc y P).mpr
      ⟨cO E π, Ideal.mem_primeCompl_iff.mpr (h.conj_notMem hP), ?_⟩⟩
    · refine (hI _).mpr ⟨π * q, ?_⟩
      rw [map_mul, hq]
      field_simp
      try ring
    · rw [rll_baseLb_eq n h, rll_mem_dLat]
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [Pi.smul_apply, Algebra.smul_def]
        exact mul_mem ⟨cO E π, rfl⟩ (h1 i hi)
      · rw [Pi.smul_apply, Algebra.smul_def, ← hb]
        refine (hI _).mpr ⟨q, ?_⟩
        rw [hq]
        field_simp
        try ring

end Pi2

end Formalism.L2.Col
