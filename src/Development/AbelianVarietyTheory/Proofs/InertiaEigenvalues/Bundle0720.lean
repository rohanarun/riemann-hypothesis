module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0714
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0633
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Formalism.AdmissibleDesigns.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0709
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharRestrictMaxRealValEqProdAbove
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

namespace GlobalTheory.PolChar

open Formalism.L2.Host

section Comp

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def ideleInf : (AdeleRing (𝓞 E) E)ˣ →* InfiniteAdeleRing E :=
  (MonoidHom.fst _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E))

def ideleAt (u : HeightOneSpectrum (𝓞 E)) : (AdeleRing (𝓞 E) E)ˣ →* u.adicCompletion E :=
  (RestrictedProduct.evalMonoidHom _ u).comp
    ((MonoidHom.snd _ _).comp (Units.coeHom (InfiniteAdeleRing E × FiniteAdeleRing (𝓞 E) E)))

theorem ideleMap_localIdele_atFin (v : HeightOneSpectrum (𝓞 F)) (a : Fˣ) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap F E (Neutral.B1.localIdele F v (atFin v a)) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.localIdele E w (atFin w (upF F a)) := by
  classical
  refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
  · refine Eq.trans ?_ (map_prod (ideleInf E) _ _).symm
    refine Eq.trans ?_ (Finset.prod_eq_one fun w _ => rfl).symm
    exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E)
  · refine Eq.trans ?_ (map_prod (ideleAt E u) _ _).symm
    change GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E u
        (Neutral.B1.finiteSingle F v (algebraMap F _ (a : F)) (u.under (𝓞 F))) =
      ∏ w ∈ aboveF (L := E) F v, Neutral.B1.finiteSingle E w (algebraMap E _ (algebraMap F E a)) u
    by_cases h : u.under (𝓞 F) = v
    · have hu : u ∈ aboveF (L := E) F v := by simp [aboveF, h]
      rw [Finset.prod_eq_single_of_mem u hu fun w _ hw => GlobalTheory.LFun.finSingle_ne (Ne.symm hw) _,
        GlobalTheory.LFun.finSingle_self]
      subst h
      rw [GlobalTheory.LFun.finSingle_self, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    · rw [GlobalTheory.LFun.finSingle_ne h, map_one]
      refine (Finset.prod_eq_one fun w hw => GlobalTheory.LFun.finSingle_ne ?_ _).symm
      rintro rfl
      exact h (by simpa [aboveF] using hw)

end Comp

end GlobalTheory.PolChar

namespace GlobalTheory.PolChar

open Formalism.L2.Host

theorem resReal_val_eq_prod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  intro E _ _ _ ν v hv
  have key : ∀ w ∈ aboveF (L := E) (maximalRealSubfield E) v,
      ν.loc w (atFin w (upF (maximalRealSubfield E) (unif v))) = ν.val w := by
    intro w hw
    obtain ⟨hunr, he⟩ := hv w hw
    refine HChar.val_eq ν hunr _ ?_
    have hu : w.under (𝓞 (maximalRealSubfield E)) = v := by simpa [aboveF] using hw
    have h1 := unif_spec v
    unfold IsUnifAt at h1 ⊢
    change Valued.v (((algebraMap (maximalRealSubfield E) E ((unif v : (maximalRealSubfield E)ˣ) :
      maximalRealSubfield E)) : E) : w.adicCompletion E) = _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', GlobalTheory.LFun.valuation_up hu, he, pow_one]
    change Valued.v (((unif v : (maximalRealSubfield E)ˣ) : maximalRealSubfield E) :
      v.adicCompletion (maximalRealSubfield E)) = _ at h1
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
  show (resReal ν).1 (Neutral.B1.localIdele _ v (atFin v (unif v))) = _
  rw [resReal_apply, ideleMap_localIdele_atFin, map_prod]
  exact Finset.prod_congr rfl key

end GlobalTheory.PolChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertFrameConjExtendsAndFrameMapSurjectiveStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_frame_conj_extends_and_frame_map_surjective : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), 0 < n → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (Dv : InertDatum L n v w) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → Formalism.UG.cT Dv.σw b.val * b.val = Formalism.UG.antiJ (w.adicCompletion L) n → ∀ p : locU n w →* Formalism.UG.GU Dv.σw n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) ∧ Function.Surjective p := by
  first | exact @GlobalTheory.InertFrameConj.conj_and_surjective | exact GlobalTheory.InertFrameConj.conj_and_surjective | (intros; apply GlobalTheory.InertFrameConj.conj_and_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalOfJacquetMin
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.JacMinCusp

open GlobalTheory.SmGL.CuspMax Matrix
open scoped TensorProduct

theorem blk_two_stdSum {a b n : ℕ} (h : a + b = n) (i : Fin n) :
    blk (two (stdSum h)) i = decide (a ≤ (i : ℕ)) := by
  obtain ⟨x, rfl⟩ := (stdSum h).surjective i
  rcases x with x | x
  · rw [← two_false, blk_apply]; simp [x.2]
  · rw [← two_true, blk_apply]; simp

theorem blk_two_stdSum_lt {a b n : ℕ} (h : a + b = n) (i j : Fin n) :
    blk (two (stdSum h)) i < blk (two (stdSum h)) j ↔ (i : ℕ) < a ∧ a ≤ (j : ℕ) := by
  rw [blk_two_stdSum, blk_two_stdSum]
  by_cases h1 : a ≤ (i : ℕ) <;> by_cases h2 : a ≤ (j : ℕ) <;> simp [h1, h2] <;> omega

theorem mem_unipRad_two_iff {R : Type} [CommRing R] {a b n : ℕ} (h : a + b = n) {g : GL (Fin n) R} :
    g ∈ unipRad R (two (stdSum h)) ↔ ∀ i j : Fin n, ¬ ((i : ℕ) < a ∧ a ≤ (j : ℕ)) →
      (g : Matrix (Fin n) (Fin n) R) i j = (1 : Matrix (Fin n) (Fin n) R) i j := by
  rw [mem_unipRad_iff_entries]
  simp only [blk_two_stdSum_lt]

end GlobalTheory.JacMinCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions

namespace GlobalTheory.TypeVec

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : GAf L n →* Module.End ℂ (GAf L n → ℂ) where
  toFun h := Formalism.L2.NG.rt L n h
  map_one' := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt]
  map_mul' a b := by
    apply LinearMap.ext; intro f; funext g
    simp [Formalism.L2.NG.rt, mul_assoc]

def IsLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (y : GL (Fin n) ℤ_[g]) (x : GAf L n) : Prop :=
  TrivOutside {s.v} (x : GA L n) ∧ s.loc n x = Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y)

attribute [local instance] GlobalTheory.TypeRec.factG

def KFix (D : D7) (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E)
    (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E))
    {A : Type} [AddCommGroup A] [Module ℂ A] (ρA : GAf D.host.E D.R.r →* Module.End ℂ A) : Submodule ℂ A :=
  ⨅ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r)
    (_ : IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x), LinearMap.ker (ρA x - LinearMap.id)

end GlobalTheory.TypeVec

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientComp
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

section Transport

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem continuous_glMap {n : Type} [Fintype n] [DecidableEq n] (j : k' →+* k) (hj : Continuous j) :
    Continuous (Matrix.GeneralLinearGroup.map (n := n) j) :=
  Units.continuous_iff.2 ⟨continuous_matrix fun a b => hj.comp (Units.continuous_val.matrix_elem a b),
    continuous_matrix fun a b => hj.comp (Units.continuous_coe_inv.matrix_elem a b)⟩

theorem glMap_surjective {n : Type} [Fintype n] [DecidableEq n] (i : k ≃+* k') :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom) := fun g =>
  ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] in
theorem isSubquotient_comp {G G' V W : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (ψ : G' →* G) :
    IsSubquotient (σ.comp ψ) (ρ.comp ψ) := by
  obtain ⟨S, f, hf⟩ := h
  exact ⟨⟨S.toSubmodule, fun g _ hv => S.apply_mem_toSubmodule (ψ g) hv⟩, ⟨f.toLinearMap, fun g => f.isIntertwining' (ψ g)⟩, hf⟩

def trGL (i : k ≃+* k') (hi' : Continuous i.symm) (x : IrrGL (k := k)) : IrrGL (k := k') :=
  IrrGL.of (x.rep.comp (Matrix.GeneralLinearGroup.map (n := Fin x.1) i.symm.toRingHom))
    (fun v => (x.2.rep.smooth v).preimage (continuous_glMap _ hi'))
    (GlobalTheory.CuspRep.ParLaws.isIrreducible_comp x.2.rep.irr _ (glMap_surjective i))

theorem hasSupport_comp (i : k ≃+* k') (hi : Continuous i) (hi' : Continuous i.symm) {N : ℕ} {V : Type}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V} {s : Multiset (IrrGL (k := k))}
    (h : HasSupport π s) :
    HasSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (s.map (trGL i hi')) := by
  obtain ⟨c, x, rfl, hir, hc, e, hsub⟩ := h
  have H : IsCuspSupport (π.comp (Matrix.GeneralLinearGroup.map (n := Fin N) i.symm.toRingHom)) (fun a => (x a).1)
      (fun a => (x a).rep.comp (Matrix.GeneralLinearGroup.map (n := Fin (x a).1) i.symm.toRingHom)) := by
    refine ⟨GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hir _ (glMap_surjective i), fun a =>
      ⟨(hc a).1, GlobalTheory.CuspRep.ParLaws.isIrreducible_comp (hc a).2.1 _ (glMap_surjective i),
        GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv i hi' _ (hc a).2.2⟩, e, ?_⟩
    obtain ⟨φ⟩ := GlobalTheory.T.parabolicInduction_comp_generalLinearGroupMapOfFieldEquiv i hi hi' (_root_.GlobalTheory.SplitWeil.nabs_map_of_homeomorph i hi hi') e (fun a => (x a).rep)
    exact (isSubquotient_comp hsub _).trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have := hasSupport_of_isCuspSupport H
  rw [Multiset.map_map]
  exact this

end Transport

end GlobalTheory.SuppIne

namespace GlobalTheory.SuppIne

open GlobalTheory.LocGL GlobalTheory.SmGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem continuous_symm {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) : Continuous (I.i k v).symm := by
  letI := (I.i k v).toRingHom.toAlgebra
  have : ContinuousSMul ℚ_[D.host.g k] ((D.naut.plGw k v).adicCompletion D.host.E) :=
    continuousSMul_of_algebraMap _ _ (I.cont k v)
  let el : ℚ_[D.host.g k] ≃ₗ[ℚ_[D.host.g k]] (D.naut.plGw k v).adicCompletion D.host.E :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (I.i k v).bijective
  refine el.toContinuousLinearEquiv.symm.continuous.congr fun y => (I.i k v).injective ?_
  exact (el.toContinuousLinearEquiv.apply_symm_apply y).trans ((I.i k v).apply_symm_apply y).symm

def tr {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : IrrRep (GL (Fin n) ((D.naut.plGw k v).adicCompletion D.host.E)) :=
  ⟨ρ, ρ.ρ.comp (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom),
    fun x => (hs x).preimage (continuous_glMap _ (continuous_symm I k v)),
    GlobalTheory.CuspRep.ParLaws.isIrreducible_comp hi _ (glMap_surjective _)⟩

theorem iso_pull {D : D7} (I : Ident D) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ} (ρ : Rep.{0} ℂ (GL (Fin n) ℚ_[D.host.g k]))
    (hs : GlobalTheory.PRep.IsSmooth ρ.ρ) (hi : ρ.ρ.IsIrreducible) : Nonempty (ρ ≅ pull I k v (tr I k v ρ hs hi)) := by
  have hg : ∀ g : GL (Fin n) ℚ_[D.host.g k], Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun a b => (I.i k v).symm_apply_apply _)
  refine ⟨Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ ρ) fun g => LinearMap.ext fun x => ?_)⟩
  change ρ.ρ g x = ρ.ρ (Matrix.GeneralLinearGroup.map (I.i k v).symm.toRingHom
      (Matrix.GeneralLinearGroup.map (I.i k v).toRingHom g)) x
  rw [hg]

end GlobalTheory.SuppIne

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientUnramPrinSeriesOfHasSupport
section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.PermPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]⟩

theorem permGL_conj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (g : Matrix (Fin n) (Fin n) k) (σ i) (σ j) := by
  have : ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      σ.toPEquiv.toMatrix * (g : Matrix (Fin n) (Fin n) k) * σ.symm.toPEquiv.toMatrix := rfl
  rw [this, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

theorem constEquiv_piTensor_detRep {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (L : ∀ _ : Fin n, GL (Fin 1) k)
    (t : ⨂[ℂ] _ : Fin n, ℂ) :
    PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ (piTensor (fun a => detRep (Fin 1) (χ a)) L t) =
      (∏ a, (χ a (GeneralLinearGroup.det (L a)) : ℂ)) * PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, piTensor_tprod, PiTensorProduct.constantBaseRingEquiv_tprod, detRep, ofChar_apply,
      detChar_apply, Finset.prod_mul_distrib, smul_eq_mul]
    ring
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), mul_add]

theorem isSubquotient_multiProd_prinSeries {n : ℕ} (e : (Σ _ : Fin n, Fin 1) ≃ Fin n)
    (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (multiProd e fun a => detRep (Fin 1) (χ a)) (prinSeries χ) := by
  let f : Fin n ≃ Fin n := (Equiv.sigmaUnique (Fin n) fun _ => Fin 1).symm.trans e
  let σ : Equiv.Perm (Fin n) := f.symm
  let P : GL (Fin n) k := permGL σ
  have hf : ∀ a (i : Fin 1), e ⟨a, i⟩ = f a := fun a i => by
    rw [Subsingleton.elim i 0]; rfl
  have hq : ∀ p : parab k (points (Fin n)), P * (p : GL (Fin n) k) * P⁻¹ ∈ parab k e := fun p => by
    refine mem_parab_iff.2 fun a b i j hab => ?_
    rw [hf, hf, permGL_conj_apply]
    simpa [σ] using mem_parab_iff.1 p.2 a b () () hab
  let κ := (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv
  let Ψ : IndSp e (piTensor fun a => detRep (Fin 1) (χ a)) →ₗ[ℂ]
      IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin n)).symm.toMonoidHom) :=
    { toFun := fun F => ⟨⟨fun g => κ (F.1.1 (P * g)), fun p g => by
          let q : parab k e := ⟨P * p * P⁻¹, hq p⟩
          have e1 : P * ((p : GL (Fin n) k) * g) = (q : GL (Fin n) k) * (P * g) := by
            simp only [q, mul_assoc, inv_mul_cancel_left]
          have hdet : ∀ a, GeneralLinearGroup.det (leviProj k e q a) =
              GeneralLinearGroup.det (leviProj k (points (Fin n)) p a) := fun a => by
            ext
            simp only [GeneralLinearGroup.val_det_apply, det_unique]
            rw [leviProj_apply, leviProj_apply, hf]
            show ((P * p * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (f a) (f a) = _
            rw [permGL_conj_apply]
            simp [σ]
          have hd : deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) =
              deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) := by
            rw [deltaHalf_apply, deltaHalf_apply]
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hdet, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
          beta_reduce
          rw [e1, parInd_law]
          generalize F.1.1 (P * g) = t
          show κ ((deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) : ℂ) •
              piTensor (fun a => detRep (Fin 1) (χ a)) (leviProj k e q) t) =
            (deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂ) •
              ofChar (torusChar χ) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) p)) (κ t)
          rw [map_smul, hd, ofChar_apply, torusChar_apply]
          congr 1
          refine (constEquiv_piTensor_detRep χ _ t).trans ?_
          rw [Units.coe_prod]
          congr 1
          exact Finset.prod_congr rfl fun a _ => by rw [hdet]; rfl⟩,
        MultiIrr.mem_smooth_of_eventually _ ((MultiIrr.eventually_of_smooth F).mono fun u hu x => by
          show κ (F.1.1 (P * (x * u))) = κ (F.1.1 (P * x))
          rw [← mul_assoc, hu])⟩
      map_add' := fun F G => Subtype.ext (Subtype.ext (funext fun x => map_add κ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => map_smul κ _ _)) }
  refine .of_injective ⟨Ψ, fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    fun F F' h => ?_
  · show κ (F.1.1 (P * x * g)) = κ (F.1.1 (P * (x * g)))
    rw [mul_assoc]
  · refine Subtype.ext (Subtype.ext (funext fun x => κ.injective ?_))
    have h1 : κ (F.1.1 (P * (P⁻¹ * x))) = κ (F'.1.1 (P * (P⁻¹ * x))) :=
      congrFun (congrArg (fun φ => φ.1.1) h) (P⁻¹ * x)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h1

end GlobalTheory.PermPrin

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetNontrivial
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.SmGL.JacquetEmptyFirstBlock

theorem jacquet_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V),
    π.IsIrreducible → ∀ (h : 0 + n = n), Nontrivial (Jacquet π (unipRad k (two (stdSum h)))) := by
  intro k _ _ _ _ n V _ _ π hπ h
  have key : ∀ x, GlobalTheory.SmGL.blk (two (stdSum h)) x = true := by
    intro x
    unfold GlobalTheory.SmGL.blk
    obtain ⟨⟨b, y⟩, hy⟩ : ∃ p, (two (stdSum h)).symm x = p := ⟨_, rfl⟩
    rw [hy]
    cases b
    · exact Fin.elim0 y
    · rfl
  have hbot : unipRad k (two (stdSum h)) = ⊥ := by
    by_contra hne
    obtain ⟨i, j, hij⟩ := (GlobalTheory.SmGL.CuspMax.unipRad_ne_bot_iff).1 hne
    rw [key i, key j] at hij
    exact lt_irrefl _ hij
  have hker : twKer π (⊥ : Subgroup (GL (Fin n) k)) 1 = ⊥ := by
    unfold twKer
    rw [Submodule.span_eq_bot]
    rintro w ⟨⟨g, hg⟩, v, rfl⟩
    rw [Subgroup.mem_bot] at hg
    subst hg
    simp
  have hV : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    have : IsSimpleOrder (Subrepresentation π) := hπ
    exact (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
      (Subrepresentation.ext (Subsingleton.elim _ _))
  rw [hbot]
  show Nontrivial (V ⧸ twKer π ⊥ 1)
  rw [hker]
  exact (Submodule.quotEquivOfEqBot (⊥ : Submodule ℂ V) rfl).toEquiv.nontrivial

end GlobalTheory.SmGL.JacquetEmptyFirstBlock
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthBoundOfRowConditionsAndDualityTheorems
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.InertiaEigenvalues.LengthBoundClosing

theorem stmt_closed : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : D7, Formalism.MainNotions.N.K.Rows.AllDesignConditions D → TruncatedSeriesCountingIdentities.Stmt D := by
  intro hA hB hT hE D h51
  exact ⟨_root_.GlobalTheory.LocalisationBoundAtPoint.boundAtPoint_all_localisations_of_objectConditions hA hB hT hE D h51, Formalism.MainNotions.TruncatedSeriesCountingIdentities.second_statement D⟩

end GlobalTheory.InertiaEigenvalues.LengthBoundClosing
end

