import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtSpecProof

section Sections

variable {R : Type} [CommRing R]

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp {G : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (x : Sec G U) :
    Sec.res (k ≫ g) x = Sec.res k (Sec.res g x) := by
  simp [Sec.res]

/- English proof (translation)
Establish `h` using `φ.hom.naturality g.op`. Conclude with `congrArg (fun m => m.hom x) h`.
-/
theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) := by
  have h := φ.hom.naturality g.op
  exact congrArg (fun m => m.hom x) h

end Sections

variable {q : ℕ} {C : Type 1} [Category.{0} C] {P : Probe C q} {X : Scheme.{0}}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _`. Rewrite using `[← res_comp, Y.nat]`.
-/
theorem map_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X)
    {c c' : C} (φ : c ⟶ c') :
    (((P.res i).K j).map φ).hom (Sec.res (Y.y c) a) = Sec.res (Y.y c') a := by
  change Sec.res (P.S.map φ).unop (Sec.res (Y.y c) a) = _
  rw [← res_comp, Y.nat]

/- English proof (translation)
Use function extensionality and compare the values at `s`. Establish `h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = Sec.res (Y.y (s.obj (Fin.last 1))) a` using `fun k => map_glob Y i j a _`. Express the relevant statement in the definitionally equal form `∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) • (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0`. Rewrite using `[Fin.sum_univ_two, h 0, h 1]`. Simplify using the standard rewrite rules.
-/
theorem d_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    d ((P.res i).K j) 0 (Y.glob i j a) = 0 := by
  funext s
  have h : ∀ k : Fin 2, (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) =
      Sec.res (Y.y (s.obj (Fin.last 1))) a := fun k => map_glob Y i j a _
  change ∑ k : Fin 2, (-1 : ℤ) ^ (k : ℕ) •
    (((P.res i).K j).map (GlobalTheory.CatH.toLast k s)).hom (Y.glob i j a (GlobalTheory.CatH.face k s)) = 0
  rw [Fin.sum_univ_two, h 0, h 1]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `map_res _ _ _`.
-/
theorem dvC_glob (Y : P.Pts X) (i : ℤ) (j : ℕ) (a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    (P.res i).dvC j 0 (Y.glob i j a) =
      Y.glob i (j + 1) (Sec.map ((GlobalTheory.EtC.res _ (tw q i)).d (j : ℤ) ((j + 1 : ℕ) : ℤ)) a) := by
  funext s
  exact map_res _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `map_add _ _ _`.
-/
theorem glob_add (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a + b) = Y.glob i j a + Y.glob i j b := by
  funext s
  exact map_add _ _ _

/- English proof (translation)
Use function extensionality and compare the values at `s`. Conclude with `map_sub _ _ _`.
-/
theorem glob_sub (Y : P.Pts X) (i : ℤ) (j : ℕ) (a b : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X) :
    Y.glob i j (a - b) = Y.glob i j a - Y.glob i j b := by
  funext s
  exact map_sub _ _ _

/- English proof (translation)
Establish `hcl` using `(hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)`. Establish `hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0`. Rewrite using `[dvC_glob, hcl]`. Use function extensionality and compare the values at `s`. Conclude with `map_zero _`.

Take `⟨z, hz, hst⟩` from `hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)`. Conclude with `⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩`.
-/
theorem edge_exists {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hSE : StEx) (hRB : RepBasic) (Y : P.Pts X)
    {x : Ht q (sch.obj X) j i} {a : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X} (hx : Rep x a) :
    ∃ h, (P.res i).Edge (Y.glob i j a) h := by
  have hcl := (hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)).2.1 x a hx ((j + 1 : ℕ) : ℤ)
  have hdv : (P.res i).dvC j 0 (Y.glob i j a) = 0 := by
    rw [dvC_glob, hcl]
    funext s
    exact map_zero _
  obtain ⟨z, hz, hst⟩ := hSE ℤ C P.L (P.res i) hT j 0 j (add_zero j) (Y.glob i j a) hdv (d_glob Y i j a)
  exact ⟨(cx P.L).cls z hz, z, hz, hst, rfl⟩

/- English proof (translation)
Establish `hB` using `hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)`. Establish `h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a')`. Use `(hB.2.2.1 x x a a' hx hx').2` as an intermediate fact. Rewrite `this` using `[sub_self]`. Then use the resulting hypothesis. Establish `hz` using `hB.2.2.2.1 (a - a') h0`.

Establish `hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a')`. Consider the cases of `j with`. Consider the case `zero`. Take `⟨b, hb⟩` from `hz (-1) (by norm_num)`. Use `(hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)` as an intermediate fact.

Establish `hb0 : b = 0` using `Subsingleton.elim _ _`. Establish `hz0 : a - a' = 0`. Rewrite using `[← hb, hb0]`. Conclude with `map_zero _`. Express the relevant statement in the definitionally equal form `Y.glob i 0 a - Y.glob i 0 a' = 0`.

Rewrite using `[← glob_sub, hz0]`. Use function extensionality and compare the values at `s`. Conclude with `map_zero _`. Consider the case `succ s`. Take `⟨b, hb⟩` from `hz (s : ℤ) (by push_cast; rfl)`.

Use `⟨Y.glob i s b, d_glob Y i s b, ?_⟩` and prove the remaining obligations. Rewrite using `[dvC_glob, hb, glob_sub]`. Conclude with `(hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB`.
-/
theorem edge_unique {i : ℤ} {j : ℕ} (hT : (P.res i).Good) (hEU : EdgeUniq) (hRB : RepBasic) (hRZ : ResZero)
    (Y : P.Pts X) {x : Ht q (sch.obj X) j i} {a a' : Sec ((GlobalTheory.EtC.res _ (tw q i)).X (j : ℤ)) X}
    (hx : Rep x a) (hx' : Rep x a') {h h' : H P.L j} (he : (P.res i).Edge (Y.glob i j a) h)
    (he' : (P.res i).Edge (Y.glob i j a') h') : h = h' := by
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have h0 : Rep (0 : Ht q (sch.obj X) j i) (a - a') := by
    have := (hB.2.2.1 x x a a' hx hx').2
    rwa [sub_self] at this
  have hz := hB.2.2.2.1 (a - a') h0
  have hVB : (P.res i).VB j (Y.glob i j a - Y.glob i j a') := by
    cases j with
    | zero =>
      obtain ⟨b, hb⟩ := hz (-1) (by norm_num)
      have := (hRZ (ZMod q) (tw q i) X).2.2 (-1) (by norm_num)
      have hb0 : b = 0 := Subsingleton.elim _ _
      have hz0 : a - a' = 0 := by
        rw [← hb, hb0]
        exact map_zero _
      change Y.glob i 0 a - Y.glob i 0 a' = 0
      rw [← glob_sub, hz0]
      funext s
      exact map_zero _
    | succ s =>
      obtain ⟨b, hb⟩ := hz (s : ℤ) (by push_cast; rfl)
      refine ⟨Y.glob i s b, d_glob Y i s b, ?_⟩
      rw [dvC_glob, hb, glob_sub]
  exact (hEU ℤ C P.L (P.res i) hT j _ _ h h' he he').2 hVB

/- English proof (translation)
Introduce `hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x`. Establish `hT` using `hRG hGen q C P i`. Establish `hB` using `hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)`. Establish `hex : ∀ x, ∃ h, Y.IsEt i j x h` using `fun x => by`. Take `⟨a, ha⟩` from `hB.1 x`.

Take `⟨h, hh⟩` from `edge_exists hT hSE hRB Y ha`. Conclude with `⟨h, a, ha, hh⟩`. Establish `huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h'`. Introduce and unpack `x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩`. Conclude with `edge_unique hT hEU hRB hRZ Y ha ha' he he'`.

Establish `hall : ∀ x, Y.IsEt i j x (Y.et i j x)`. Use `pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_` and prove the remaining obligations. Use `choose f hf using hex`. Use `⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩` and prove the remaining obligations. Take `⟨a, ha, he⟩` from `hf u`.

Take `⟨b, hb, he'⟩` from `hf v`. Use `⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩` and prove the remaining obligations. Rewrite using `[glob_add]`. Conclude with `(hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1`. Use `⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩` and prove the remaining obligations.

Take `⟨h, hh⟩` from `edge_exists hT hSE hRB Y ha`. Establish `e : h = Y.et i j x` using `huniq ⟨a, ha, hh⟩ (hall x)`. Rewrite using `[← e]` and apply the resulting hypothesis.
-/
theorem etSpec : ResGood → StEx → EdgeUniq → RepBasic → ResZero → EtSpec := by
  intro hRG hSE hEU hRB hRZ hGen q _ C _ P X Y i j x
  have hT := hRG hGen q C P i
  have hB := hRB (ZMod q) (GlobalTheory.EtC.res _ (tw q i)) X (j : ℤ)
  have hex : ∀ x, ∃ h, Y.IsEt i j x h := fun x => by
    obtain ⟨a, ha⟩ := hB.1 x
    obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
    exact ⟨h, a, ha, hh⟩
  have huniq : ∀ {x h h'}, Y.IsEt i j x h → Y.IsEt i j x h' → h = h' := by
    rintro x h h' ⟨a, ha, he⟩ ⟨a', ha', he'⟩
    exact edge_unique hT hEU hRB hRZ Y ha ha' he he'
  have hall : ∀ x, Y.IsEt i j x (Y.et i j x) := by
    refine pick_spec (P := fun e : Ht q (sch.obj X) j i →+ H P.L j => ∀ x, Y.IsEt i j x (e x)) ?_
    choose f hf using hex
    refine ⟨AddMonoidHom.mk' f fun u v => huniq (hf _) ?_, hf⟩
    obtain ⟨a, ha, he⟩ := hf u
    obtain ⟨b, hb, he'⟩ := hf v
    refine ⟨a + b, (hB.2.2.1 u v a b ha hb).1, ?_⟩
    rw [glob_add]
    exact (hEU ℤ C P.L (P.res i) hT j _ _ _ _ he he').1
  refine ⟨fun a ha => ?_, fun h hh => huniq hh (hall x)⟩
  obtain ⟨h, hh⟩ := edge_exists hT hSE hRB Y ha
  have e : h = Y.et i j x := huniq ⟨a, ha, hh⟩ (hall x)
  rwa [← e]

end GlobalTheory.CompanionTheory.EtSpecProof
