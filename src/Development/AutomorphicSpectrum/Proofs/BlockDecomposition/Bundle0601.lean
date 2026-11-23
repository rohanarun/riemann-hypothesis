module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.CuspPairSubGeneric
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverse
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0585

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompat
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.OmNatT

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

universe v u

theorem rep_unique {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h
  obtain ⟨f', hf', e', hz'⟩ := h'
  have hff : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst hff
  exact e.trans e'.symm

section Span

variable (K A : Type) [CommRing K] [CommRing A] [Algebra K A]

theorem multi_mem {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {a : ℕ}
    (f : (Fin a → M) →ₘₗ[A] N) (s : Set M) (hs : Submodule.span A s = ⊤) (S : Submodule A N)
    (h : ∀ v : Fin a → M, (∀ k, v k ∈ s) → f v ∈ S) (v : Fin a → M) : f v ∈ S := by
  classical
  have key : ∀ (t : Finset (Fin a)) (v : Fin a → M), (∀ k, k ∉ t → v k ∈ s) → f v ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun v hv => h v fun k => hv k (by simp)
    | insert i t hi ih =>
      intro v hv
      have hvi : v i ∈ Submodule.span A s := hs ▸ Submodule.mem_top
      have : ∀ x ∈ Submodule.span A s, f (Function.update v i x) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hxs =>
          refine ih _ fun k hk => ?_
          by_cases e : k = i
          · rw [e, Function.update_self]; exact hxs
          · rw [Function.update_of_ne e]
            exact hv k (by simp [e, hk])
        | zero => rw [f.map_update_zero]; exact S.zero_mem
        | add x y _ _ hx hy => rw [f.map_update_add]; exact S.add_mem hx hy
        | smul c x _ hx => rw [f.map_update_smul, RingHom.id_apply]; exact S.smul_mem _ hx
      simpa using this _ hvi
  exact key Finset.univ v fun k hk => (hk (Finset.mem_univ k)).elim

theorem span_form (a : ℕ) : Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} = ⊤ := by
  set S := Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} with hS
  have hsm : ∀ (c : A) x, x ∈ S → c • x ∈ S := by
    intro c x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, rfl⟩ := hx
      refine Submodule.subset_span ⟨c * g₀, g, ?_⟩
      simp only [CrystallineSemistableComparison.Onto.form, mul_smul]
    | zero => rw [smul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact S.add_mem hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul A r x, smul_comm, algebraMap_smul]
      exact S.smul_mem r hx
  let S' : Submodule A (⋀[A]^a Ω[A⁄K]) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := hsm }
  have hι : ∀ v : Fin a → Ω[A⁄K], exteriorPower.ιMulti A a v ∈ S' := fun v =>
    multi_mem A (exteriorPower.ιMulti A a (M := Ω[A⁄K])).toMultilinearMap (Set.range (KaehlerDifferential.D K A))
      (KaehlerDifferential.span_range_derivation K A) S' (fun v hv => by
        choose g hg using hv
        refine Submodule.subset_span ⟨1, g, ?_⟩
        have e : v = fun k => KaehlerDifferential.D K A (g k) := (funext hg).symm
        simp only [CrystallineSemistableComparison.Onto.form, one_smul]
        rw [← e]
        rfl) v
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have : Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) ≤ S' :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hι v)
  exact this hx

end Span

section Mom

variable {R R' B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing R'] [CommRing B'] [Algebra R' B']
  {σ : R →+* R'} {α : B →+* B'}

theorem mOm_form (h : SemiHom σ α) {a : ℕ} (g₀ : B) (g : Fin a → B) :
    h.mOm a (CrystallineSemistableComparison.Onto.form R g₀ g) = CrystallineSemistableComparison.Onto.form R' (α g₀) fun k => α (g k) := by
  unfold CrystallineSemistableComparison.Onto.form
  rw [h.mOm_smul]
  congr 1
  refine Subtype.ext ?_
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (h.mDR_ι _).trans (congrArg (ExteriorAlgebra.ι B') (h.m1_D (g i)))

end Mom

section Pull

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def outL (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Quotient.out (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Ideal.Quotient.mk_out _

variable {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

def uS (u : X ⟶ Y) : Γ(Y, ⊤) →+* Γ(X, ⊤) := (u.appLE ⊤ ⊤ (by simp)).hom

theorem ev_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := p) (κ := Ideal.Quotient.mk ⊥) ((smS u hu).G.obj T) (inTop p _) g =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) (uS u g) := by
  change (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T ≫ u).appLE ⊤ ⊤ _).hom g) =
    (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE ⊤ ⊤ _).hom ((u.appLE ⊤ ⊤ (by simp)).hom g))
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ ⊤ (by simp) (by simp)]
  rfl

theorem out_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    (outL p).v ((smS u hu).G.obj T) g = (outL q).v T (uS u g) :=
  congrArg Quotient.out (ev_pull u hu T g)

theorem form_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤))
    (s : ComposableArrows (Thick (smFun X q)) a) :
    (outL q).form (uS u g₀) (fun k => uS u (g k)) s = (outL p).form g₀ g (s ⋙ (smS u hu).G) := by
  unfold LiftsT.form
  refine congrArg₂ (· * ·) (out_pull u hu _ g₀).symm (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg₂ (· - ·) (congrArg _ (out_pull u hu _ (g k)).symm) (congrArg _ (out_pull u hu _ (g k)).symm)

theorem rep_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ}
    {z : ∀ s : ComposableArrows (Thick (smFun Y p)) a, (s.obj (Fin.last a)).B}
    {z' : ∀ s : ComposableArrows (Thick (smFun X q)) a, (s.obj (Fin.last a)).B}
    (hz : ∀ s, z' s = z (s ⋙ (smS u hu).G)) {c : Hdg p a a}
    (h : Rep (thFil (smFun Y p) (a : ℤ)) (thFil (smFun Y p) ((a : ℤ) + 1)) z (show CH.H (grT (smFun Y p) a) a from c)) :
    Rep (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) z'
      (show CH.H (grT (smFun X q) a) a from pullH u hu a a c) := by
  obtain ⟨f, hf, e, hfz⟩ := h
  let m : CH.Mor (grT (smFun Y p) a) (grT (smFun X q) a) (RingHom.id K) :=
    (smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx
  have hd : CH.d (grT (smFun X q) a) a (m.pullC a f) = 0 := by
    rw [m.d_pullC, hf, map_zero]
  refine ⟨m.pullC a f, hd, ?_, fun s => ?_⟩
  · change m.pull a c = _
    have : c = (CH.cx (grT (smFun Y p) a)).cls f hf := e
    rw [this]
    exact CrystallineSemistableComparison.P.mapH_cls m.hom a f hf hd
  · rw [hz s]
    exact congrArg (Ideal.quotientMap _ ((smS u hu).ρ _) _) (hfz (s ⋙ (smS u hu).G))

end Pull

section Main

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem res_pull_form (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤)) :
    formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (gForm p g₀ g)) =
      gForm q (uS u g₀) fun k => uS u (g k) := by
  have e1 : formPull hu ⊤ a (gForm p g₀ g) = CrystallineSemistableComparison.Onto.form K (A := Sec q (u ⁻¹ᵁ ⊤)) (appSec p q u ⊤ g₀)
      fun k => appSec p q u ⊤ (g k) := mOm_form (semiHom_appSec hu ⊤) g₀ g
  rw [e1]
  exact mOm_form (SemiHom.of_algHom (Sec.res q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp))) _ _

end Main

theorem pull_nat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  intro K _ X Y q p u hu a e e' he he' x
  have key : ∀ ω : OmU p ⊤ a, e (pullH u hu a a (e'.symm ω)) =
      formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a ω) := by
    intro ω
    have hω : ω ∈ Submodule.span K {ω : ⋀[Sec p ⊤]^a Ω[Sec p ⊤⁄K] | ∃ (g₀ : Sec p ⊤) (g : Fin a → Sec p ⊤),
        ω = CrystallineSemistableComparison.Onto.form K g₀ g} := by
      rw [span_form]; trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨g₀, g, rfl⟩ := hω
      have h1 := he' g₀ g (outL p)
      have h2 := he (uS u g₀) (fun k => uS u (g k)) (outL q)
      have h3 := rep_pull u hu (fun s => form_pull u hu g₀ g s) h1
      have h4 : pullH u hu a a (e'.symm (gForm p g₀ g)) = e.symm (gForm q (uS u g₀) fun k => uS u (g k)) :=
        rep_unique h3 h2
      refine Eq.trans ?_ (res_pull_form u hu g₀ g).symm
      change e (pullH u hu a a (e'.symm (gForm p g₀ g))) = _
      rw [h4, LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul r x _ hx =>
      simp only [map_smul, hx]
  simpa using key (e' x)

end GlobalTheory.CompanionTheory.OmNatT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralHermitianInvariance
section
noncomputable section

namespace GlobalTheory.CompanionTheory.GunrInv

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen
  PositivityTheory.SiegelWeilFormula.Gunr Filter
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trPair_add_left (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R (A + B) C = trPair (F := F) (E := E) R A C + trPair (F := F) (E := E) R B C := by
  simp only [trPair, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _), mul_add]

theorem trPair_add_right (R : Type) [CommRing R] [Algebra F R] {n : ℕ}
    (A B C : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    trPair (F := F) (E := E) R A (B + C) = trPair (F := F) (E := E) R A B + trPair (F := F) (E := E) R A C := by
  simp only [trPair, Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem multiplicity_add_lattice_preserving {R : Type} [CommRing R] [MeasurableSpace R] {n : ℕ} (lam : Measure (Fin n → R))
    (L : AddSubgroup (Fin n → R)) (b h : Matrix (Fin n) (Fin n) R) (hh : ∀ y ∈ L, h.mulVec y ∈ L) :
    nu2 lam L L (b + h) = nu2 lam L L b := by
  have e : {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + (b + h).mulVec y'} = {x | ∃ y ∈ L, ∃ y' ∈ L, x = y + b.mulVec y'} := by
    ext x
    constructor
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y + h.mulVec y', L.add_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
    · rintro ⟨y, hy, y', hy', rfl⟩
      refine ⟨y - h.mulVec y', L.sub_mem hy (hh y' hy'), y', hy', ?_⟩
      rw [Matrix.add_mulVec]
      abel
  simp only [nu2, e]

section Good

variable {σ : E →ₐ[F] E} {M n d : ℕ} {J : Matrix (Fin M) (Fin M) E} {T : Matrix (Fin n) (Fin n) E}
  {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {ψv : Fv F v → ℂ} {S : Subring (Fv F v ⊗[F] E)}
  {σS : S →+* S} {ϖ : Fv F v} {ε : ℤ}

theorem trPair_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {A B : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (hA : ∀ i j, A i j ∈ S) (hB : ∀ i j, B i j ∈ S) :
    trPair (F := F) (E := E) (Fv F v) A B ∈ v.adicCompletionIntegers F := by
  have e : algebraMap F (Fv F v) (1 / 2) = (2 : Fv F v)⁻¹ := by
    rw [one_div, map_inv₀, map_ofNat]
  rw [trPair, e]
  exact mul_mem hG.half_mem (hG.trace_mem
    (sum_mem fun a _ => sum_mem fun c _ => mul_mem (hA a c) (hB c a)))

theorem gramR_mem (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) {Y : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV (M := M) (n := n) bs v) (a c : Fin n) : gramR (Fv F v) σ J Y a c ∈ S := by
  have hmem : ∀ a i, Y a i ∈ S := fun a i => by
    have : Y a i ∈ (S : Set (Fv F v ⊗[F] E)) := by
      rw [hG.carrier]
      exact fun k => hY a i k
    exact this
  have hsig : ∀ x ∈ S, sigR (Fv F v) σ x ∈ S := fun x hx => by
    have := (σS ⟨x, hx⟩).2
    rwa [hG.sig ⟨x, hx⟩] at this
  show ∑ i, ∑ j, sigR (Fv F v) σ (Y a i) * JR (Fv F v) J i j * Y c j ∈ S
  exact sum_mem fun i _ => sum_mem fun j _ =>
    mul_mem (mul_mem (hsig _ (hmem a i)) (hG.J_int i j)) (hmem c j)

theorem jtR_add (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) (b + h) = jtR (Fv F v) σ J ψv μv ((latV bs v).indicator 1) b := by
  unfold jtR
  congr 1
  funext Y
  by_cases hY : Y ∈ latV (M := M) (n := n) bs v
  · have h1 : ψv (trPair (F := F) (E := E) (Fv F v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (gramR (Fv F v) σ J Y)) = 1 :=
      hG.psi_of_mem (trPair_mem hG hh (gramR_mem hG hY))
    rw [AddSubgroup.coe_add, trPair_add_left, hG.psi_add, h1, mul_one]
  · simp [Set.indicator_of_notMem hY]

theorem character_add_integral_hermitian (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (hT : ∀ a b, σ (T b a) = T a b)
    (b h : HermR (Fv F v) σ n) (hh : h ∈ H0 S σ n) :
    ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 (b + h).1) = ψv (-trPair (Fv F v) (hermOf (Fv F v) σ T hT).1 b.1) := by
  have h1 : trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1 ∈ v.adicCompletionIntegers F :=
    trPair_mem hG (fun i j => hG.T_int i j) hh
  have h2 : ψv (-trPair (F := F) (E := E) (Fv F v) (hermOf (Fv F v) σ T hT).1 h.1) = 1 :=
    hG.psi_of_mem (neg_mem h1)
  rw [AddSubgroup.coe_add, trPair_add_right, neg_add, hG.psi_add, h2, mul_one]

theorem mulVec_mem_L (hG : GoodLoc σ J T bs v ψv S σS ϖ ε) (L : AddSubgroup (Fin n → Fv F v ⊗[F] E))
    (hL : (L : Set (Fin n → Fv F v ⊗[F] E)) = latO bs v) (h : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (hh : ∀ i j, h i j ∈ S) (y : Fin n → Fv F v ⊗[F] E) (hy : y ∈ L) : h.mulVec y ∈ L := by
  have key : ∀ w : Fin n → Fv F v ⊗[F] E, w ∈ L ↔ ∀ a, w a ∈ S := fun w => by
    have e1 : w ∈ L ↔ w ∈ (latO bs v : Set (Fin n → Fv F v ⊗[F] E)) := by
      rw [← hL]; rfl
    have e2 : ∀ x, x ∈ S ↔ x ∈ Rv bs v := fun x => by
      rw [← hG.carrier]; rfl
    rw [e1]
    simp only [e2]
    rfl
  rw [key] at hy ⊢
  intro a
  show ∑ j, h a j * y j ∈ S
  exact sum_mem fun j _ => mul_mem (hh a j) (hy j)

end Good

theorem integrand_invariant_integral_hermitian : HermitianLatticeInvariance := by
  intro F E _ _ _ _ _ σ M n d J T bs v ψv S σS ϖ ε hG hT μv lam L hL z b h hh
  unfold whI
  rw [jtR_add hG μv b h hh, character_add_integral_hermitian hG hT b h hh]
  have e : nu2 lam L L (b + h).1 = nu2 lam L L b.1 := by
    rw [AddSubgroup.coe_add]
    exact multiplicity_add_lattice_preserving lam L _ _ (mulVec_mem_L hG L hL _ hh)
  rw [e]

end GlobalTheory.CompanionTheory.GunrInv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvolutionCompatiblePolynomial
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms

namespace GlobalTheory.CompanionTheory.HermFixed

theorem dvd_of_monic_irreducible_factors {K : Type} [Field K] {P d : K[X]} (hs : P.Separable)
    (h : ∀ Q : K[X], Q.Monic → Irreducible Q → Q ∣ P → Q ∣ d) : P ∣ d := by
  by_cases hd : d = 0
  · simp [hd]
  have hP0 : P ≠ 0 := hs.ne_zero
  have hnd : (UniqueFactorizationMonoid.normalizedFactors P).Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hP0).1 hs.squarefree
  refine (UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors hP0 hd).2 ?_
  refine (Multiset.le_iff_subset hnd).2 fun Q hQ => ?_
  have hirr := UniqueFactorizationMonoid.irreducible_of_normalized_factor Q hQ
  have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor Q hQ
  have hmon : Q.Monic := by
    rw [← hnorm]
    exact Polynomial.monic_normalize hirr.ne_zero
  have hdvd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQ
  exact UniqueFactorizationMonoid.mem_normalizedFactors_iff' hd |>.2 ⟨hirr, hnorm, h Q hmon hirr hdvd⟩

theorem dvd_map_comp_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Q : SelfRecip E r)
    (m r₀ : E[X]) (hr : Q.1 ∣ X * r₀ - 1)
    (hfix : invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) :
    Q.1 ∣ (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m := by
  have h1 : AdjoinRoot.mk Q.1 (X * r₀ - 1) = 0 := AdjoinRoot.mk_eq_zero.2 hr
  rw [map_sub, map_mul, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h1
  have hR : AdjoinRoot.mk Q.1 r₀ = (AdjoinRoot.root Q.1)⁻¹ := eq_inv_of_mul_eq_one_right h1
  have hinv : invol Q (AdjoinRoot.mk Q.1 m : Fld Q)
      = AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀) := by
    show AdjoinRoot.lift ((AdjoinRoot.of Q.1).comp (IsCMField.complexConj E : E →+* E)) (AdjoinRoot.root Q.1)⁻¹
      (eval₂_conj_inv_root Q) (AdjoinRoot.mk Q.1 m) = _
    rw [AdjoinRoot.lift_mk, ← hR, Polynomial.comp, Polynomial.hom_eval₂, eval₂_map]
    rfl
  have heq : AdjoinRoot.mk Q.1 ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = AdjoinRoot.mk Q.1 m := hinv.symm.trans hfix
  refine AdjoinRoot.mk_eq_zero.1 ?_
  rw [map_sub, heq, sub_self]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) := by
  intro E _ _ _ n γ₀ hell H₀ hH _ hiso m hfix
  have hsep : γ₀.val.charpoly.Separable := hell.2.2.1
  obtain ⟨r₀, hr₀⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm γ₀.val (γ₀⁻¹).val hsep
    (by rw [Units.mul_inv, Units.inv_mul])
  have hPr : γ₀.val.charpoly ∣ X * r₀ - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval γ₀.val hsep _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr₀, Units.mul_inv, map_one, sub_self]
  have hAB : aeval γ₀.val r₀ * γ₀.val = 1 := by rw [← hr₀, Units.inv_mul]
  have key := GlobalTheory.CompanionTheory.AdjointPoly.cT_aeval_mul_eq E (IsCMField.complexConj E).toRingEquiv.toRingHom n
    γ₀.val H₀ r₀ hiso hAB m
  have hdvd : γ₀.val.charpoly ∣
      (m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m :=
    dvd_of_monic_irreducible_factors hsep fun Q hmon hirr hQ =>
      dvd_map_comp_sub ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ m r₀
        (hQ.trans hPr) (hfix _ ⟨Q, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell Q hmon hirr hQ⟩ hQ)
  have heq : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀)
      = aeval γ₀.val m := by
    obtain ⟨t, ht⟩ := hdvd
    have h0 : aeval γ₀.val ((m.map (IsCMField.complexConj E).toRingEquiv.toRingHom).comp r₀ - m) = 0 := by
      rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
    rwa [map_sub, sub_eq_zero] at h0
  have hH' : cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ = H₀ := hH
  have hmul : cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m)
      = cT (IsCMField.complexConj E).toRingEquiv.toRingHom (aeval γ₀.val m)
        * cT (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ := by
    simp only [cT, Matrix.map_mul, Matrix.transpose_mul]
  show cT (IsCMField.complexConj E).toRingEquiv.toRingHom (H₀ * aeval γ₀.val m) = H₀ * aeval γ₀.val m
  rw [hmul, hH', key, heq]

end GlobalTheory.CompanionTheory.HermFixed
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsGenericOfInjective
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.CuspStd

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def prod₂MapR {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] (π₁ : Representation ℂ (GL (Fin r) k) U)
    {π₂ : Representation ℂ (GL (Fin t) k) X} {π₂' : Representation ℂ (GL (Fin t) k) Y}
    (f : π₂.IntertwiningMap π₂') : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁ π₂') :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁ π₂')
    ⟨TensorProduct.map LinearMap.id f.toLinearMap, fun g => by
      ext u x
      exact congrArg (fun b => π₁ g.1 u ⊗ₜ[ℂ] b) (f.isIntertwining _ _ g.2 x)⟩ _)

def prod₂MapL {r t : ℕ} {U X Y : Type} [AddCommGroup U] [Module ℂ U] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] {π₁ : Representation ℂ (GL (Fin r) k) X}
    {π₁' : Representation ℂ (GL (Fin r) k) Y} (f : π₁.IntertwiningMap π₁')
    (π₂ : Representation ℂ (GL (Fin t) k) U) : (prod₂ π₁ π₂).IntertwiningMap (prod₂ π₁' π₂) :=
  parIndMap _ (compMap (ρ := extTensor π₁ π₂) (σ := extTensor π₁' π₂)
    ⟨TensorProduct.map f.toLinearMap LinearMap.id, fun g => by
      ext x u
      exact congrArg (fun b => b ⊗ₜ[ℂ] π₂ g.2 u) (f.isIntertwining _ _ g.1 x)⟩ _)

end GlobalTheory.CompanionTheory.CuspStd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocks
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace GlobalTheory.CompanionTheory.JacTheta

theorem nonempty_jac_comp_thetaW : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  intro k _ _ _ _ h N d hd hd' V _ _ π
  exact ⟨GlobalTheory.CompanionTheory.JmThetaInv.jacCompThetaW d hd hd' π⟩

end GlobalTheory.CompanionTheory.JacTheta
end

