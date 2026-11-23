module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0634
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0649
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0627
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0644
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0656
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0653
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0654
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndicesPairingLengthsVanishOffTwistedPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
public import Formalism.LocalToGlobal.Divisibility.InertPartitionLePartF

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AgreeOfData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdAgree

open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting.Up.RealOfReading

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem agree_of_data (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) {cf : CharFrame D} {nch : NChoice D}
    (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) (hb htup hg hf)
    (M : MtFam D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) (hrep : ∀ σ, (rep σ).Iso (principalLevelFrame.rowRepR R.θ (Y.eFT σ)))
    (c : ∀ i, CoefA (Vc D i)) (hc : R.cV = c) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (std : ∀ i, R3.StdFrame Y.hF (PV i))
    (eW : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, (M μ (i.1 + 1) (by omega) (by omega)).wt.W ≃ₗ[ℂ] (c i).W)
    (jm : ∀ μ, Used0 D μ → ∀ i : Fin D.R.m, D.what₂.Mt μ (i.1 + 1) → GA D (Vc D i) → (c i).W)
    (hj : ∀ μ h i x, HEq (Y.IL.jMt μ h i x).1 (jm μ h i x))
    (read : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (x : D.what₂.Mt μ (i.1 + 1)) (g : GAf D.host.E D.R.nV),
      eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = jm μ h i x ((PV i).ψ g))
    (rat : ∀ (i : Fin D.R.m) (g : GAf D.host.E D.R.nV), g ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV ↔
      ∃ γ ∈ Formalism.L2.Theta.GQ (Vc D i), finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g))
    (wt : ∀ μ (h : Used0 D μ) (i : Fin D.R.m) (g : ReciprocityTheory.Aut.GQ D.host.E D.R.nV), ∀ γ ∈ Formalism.L2.Theta.GQ (Vc D i),
      finHom (Vc D i) γ = finHom (Vc D i) ((PV i).ψ g) → ∀ v,
        eW μ h i ((M μ (i.1 + 1) (by omega) (by omega)).wt.ρ g v) = (c i).ρ γ (eW μ h i v)) :
    Nonempty (GlobalTheory.NJoin.Agree (realOfRead R.toRealDat F.lv2 Y tp hC Xd E labPi hb htup hg hf) M rep) := by
  subst hc
  refine ⟨⟨Y.hF, PV, fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (std j), fun j => (StandardFrameAgreement.stdFrame_iff _ _).1 (Y.stdPsi.2 j),
    fun _ => 1, ?_, fun μ hμ j => (eW μ hμ j).symm, ?_, ?_, hrep⟩⟩
  · intro j h
    simp only [inv_one, one_mul, mul_one]
    exact rat j h
  · intro μ hμ j h γ hγ he v
    have he' := he
    simp only [inv_one, one_mul, mul_one] at he'
    have key := wt μ hμ j h γ hγ he' ((eW μ hμ j).symm v)
    refine (LinearEquiv.symm_apply_eq _).2 ?_
    refine Eq.trans ?_ key.symm
    exact congrArg _ (LinearEquiv.apply_symm_apply _ v).symm
  · intro μ hμ j x h
    refine (LinearEquiv.eq_symm_apply _).2 ?_
    refine (read μ hμ j x h).trans ?_
    simp only [inv_one, one_mul]
    exact (congrFun (eq_of_heq (hj μ hμ j x)) _).symm

theorem heq_apply {Mt : D.what₂.Tup → ℕ → Hs} {c c' : ∀ i, CoefA (Vc D i)} (h : c = c')
    (j : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c i).W))
    (j' : ∀ μ (i : Fin D.R.m), (Mt μ ((i : ℕ) + 1)).T →ₗ[ℂ] (GA D (Vc D i) → (c' i).W)) (hj : HEq j j') (μ i x) :
    HEq (j μ i x) (j' μ i x) := by
  subst h
  cases hj
  rfl

end Gen

section Copy

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {px : PreX B.toPre} {I : ColIn B px} {hX : B.fields.Ok} {T : TwDat B}
  {Wt : Set B.places.Pl}

def cpR (z : Dat a.st I hX T Wt) :
    @RealDat3 b.st.toD7 _ _ _ _ _ _ (famR b.st I hX (usedOf I T Wt) z.Xg z.tr) (coreJ b z.core).Q.c.F _ _ ((by exact @alg B C a b (↥(@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@IntermediateField.toField Rat Complex Rat.instField Complex.instField (@DivisionRing.toRatAlgebra Complex (@Field.toDivisionRing Complex Complex.instField) Complex.instCharZero) (@ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff.F (@Formalism.HC.HostRaw.E (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instField (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (@Formalism.HC.HostRaw.instNF (@Late.st B C a).toD7.R.toFrame (@Formalism.HC.HostAx.toHostRaw (@Late.st B C a).toD7.R.toFrame (@Host.toHostAx (@Late.st B C a).toD7.R (@Late.st B C a).toD7.host))) (Pj.instCMHost (@Late.st B C a).toD7) (@Pj.Par.H (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.l (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))) (@Pj.Par.c (@Late.st B C a).toD7 (@Pj.Core.Q (@Late.st B C a).toD7 (@Pj.CoreJ.toCore (@Late.st B C a).toD7 (@Dat.core (@Late.st B C a) px I hX T Wt z)))))) (@Dat.alg (@Late.st B C a) px I hX T Wt z))) :=
  (by with_unfolding_all exact ((real3 b (iK := z.alg) z.R) :))

def cpV (c : ∀ i, CoefA (Vc a.D i)) : ∀ i, CoefA (Vc b.D i) := fun i => (by with_unfolding_all exact ((coefA b (c ((by with_unfolding_all exact (i :))))) :))

theorem cV_copy (z₀ : Dat a.st I hX T Wt) (z : Dat b.st I hX T Wt) (h1 : z.Xg = z₀.Xg) (h2 : z.tr = z₀.tr)
    (h3 : HEq z.core (coreJ b z₀.core)) (h4 : HEq z.R (real3 b (iK := z₀.alg) z₀.R)) : z.R.cV = cpV b z₀.R.cV := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4
  subst h1 h2
  obtain rfl : core = coreJ b z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg b z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR b z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR b z₀)) :))))
  exact (by with_unfolding_all exact ((Eq.refl (cpV b z₀.R.cV)) :))

theorem cV_two (b' : Late B C) {c₀ : ∀ i, CoefA (Vc a.D i)} {c : ∀ i, CoefA (Vc b.D i)} {c' : ∀ i, CoefA (Vc b'.D i)}
    (h : c = cpV b c₀) (h' : c' = cpV b' c₀) : c' = cpV b' c := by
  subst h h'
  exact (by with_unfolding_all exact ((Eq.refl (cpV b' c₀)) :))

end Copy

section Main

theorem iso_of_eq {Lf : Type} [Field Lf] [NumberField Lf] [IsCMField Lf] {n : ℕ} {π π' : NG.FinTyp Lf n} (h : π = π') : π.Iso π' :=
  h ▸ NG.IsoRep.refl _


end Main

end GlobalTheory.HeightCounting.Up.ThirdAgree

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarriedThTw
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain GlobalTheory.HeightCounting GlobalTheory.TwistChoice

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev thTw (D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) : TwNew D :=
  ⟨D.ntw, D.nexp, D.nStage_trivialCharacter_coeff_eq, th, D.ntwbr, D.ntwbr_ind⟩

theorem carried_thTw (D0 D : D7) (th : NTh D.R D.host D.what₂ D.LL0 D.nd D.ntw D.nexp) (h : Carried D0 D) :
    Carried D0 (thTw D th).toD7 :=
  ⟨⟨{ h.exp.gal with }, { h.exp.set with }, { h.exp.frm with }, h.exp.br, h.exp.av⟩, h.emb⟩

end GlobalTheory.HeightCounting.Up

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.CenAtLoc

theorem mapCoef_mem_center' {R S G : Type} [CommRing R] [CommRing S] [Group G] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : ∀ a, z * a = a * z) :
    Formalism.MainNotions.PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    have e : MonoidAlgebra.of S G m = MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of R G m) := by
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
    rw [e]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem zlStable_of_allT {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T D.R.m} {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G}
    {ψ1 : P1 →* D.what₂.LLˣ} {X0 : BaseLevelRowSide D} {tp : D.what₂.Tup → T} {eG : G ≃* G0g D.nd}
    (h : AllT D A P0 ψ0 P1 ψ1 X0 tp eG) : GlobalTheory.PendOf.ZLStable D := by
  intro i z hz x
  have hc := mapCoef_mem_center' D.what₂.embLL z hz
  have key : ∀ (μ : D.what₂.Tup) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ x : D.what₂.MtL μ j, ∃ y : D.what₂.MtL μ j,
      D.what₂.jMt μ j y = D.ntypes.cenMt μ j ⟨_, hc⟩ (D.what₂.jMt μ j x) := by
    intro μ j h1 h2 x
    obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
    let a : MonoidAlgebra D.what₂.LL G := MonoidAlgebra.ofCoeff (Finsupp.equivMapDomain eG.symm.toEquiv z.coeff)
    have ha : ∀ g : G, D.what₂.embLL (a.coeff g) =
        ((⟨_, hc⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) : MonoidAlgebra ℂ (G0g D.nd)).coeff (eG g) := by
      intro g
      simp [a, Formalism.MainNotions.PairedCharacterCondition.mapCoef, Finsupp.equivMapDomain_apply]
    obtain ⟨-, -, h3⟩ := h.cen μ ⟨_, hc⟩ a ha
    have := h3 k ((h.eMt k μ).symm x)
    refine ⟨h.eMt k μ (((A.fam.L k (tp μ)).S.lvlOp (A.fam.L k (tp μ)).r (A.fam.lvlA P0 ψ0).P (A.fam.lvlA P0 ψ0).ψ a).mulVec ((h.eMt k μ).symm x)), ?_⟩
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨y, hy⟩ := key (D.nd.mu i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2 x
  refine ⟨y, ?_⟩
  rw [hy]
  unfold NTypes.onMt
  rw [dite_eq_left hc]

end GlobalTheory.CenAtLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.DTheta


set_option maxHeartbeats 4000000 in
theorem composite_eq_lift : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  intro hC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPins hHolds
  have hch : R.toRealDat.IsChain := RealDat.chain_of_weak hPins.char.base.chain hHolds.aux.ex
  have hS : StepLev R.toRealDat F.lv2 := _root_.GlobalTheory.Mem.R3.DTheta.stepLev_holds hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hT : TopLev R.toRealDat F.lv2 := _root_.GlobalTheory.Mem.R3.DTheta.topLev_holds hC D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hP : RowProj R.toRealDat F.lv2 := rowProj_holds hC.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG hPins hHolds
  have hUsed : ∀ t, Used0 D (Y.tup t) := by
    intro t
    rcases hPins.char.tup.mu_used t with h | ⟨w, hw⟩
    · left
      rw [h]
      exact Y.tup0
    · right
      refine ⟨D.plEq.symm w, ?_⟩
      rw [Y.muAt, Equiv.apply_symm_apply, hw]
  refine ⟨fun t x => ?_, fun t x => ?_⟩
  · rw [iota_sharp]
    exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP (RowSide.sharp D) true Y.Ish Y.tied.sharp
      (Y.tup t) (hUsed t) (Y.jA t x) t (Y.tupT_tup t) _ (Y.topRead t (hUsed t) x)
  · exact iota_eq_real' R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop hch hS hT hP X0.s false Y.Iz Y.tied.base
      (Y.tup t) (hUsed t) (Y.jA0 t x) t (Y.tupT_tup t) _ (Y.topRead0 t (hUsed t) x)

end GlobalTheory.Mem.R3.DTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenAdjointOfReadRelation
section
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}


variable (R) in
def EigVec (i : Fin D.R.m) (k : ℕ) (Q : PlE D.host) (Rr : Finset (GA D (Wc D i))) (c : ↥D.LL0) (v : (R.HW i (sg0 D A3.A)).H) : Prop :=
  hkNorm R i k Q • heckeOn (R.MW i (sg0 D A3.A)) Rr ((R.HW i (sg0 D A3.A)).e v) =
    D.what₂.embLL ((c : ↥D.LL0) : D.what₂.LL) • (R.HW i (sg0 D A3.A)).e v

theorem eigAd_iff_eigVec (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Sb : Finset (PlE D.host))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) : EigAd Y Sb eig ↔
    ∀ (i : Fin D.R.m) σ k Q α Rr, HkDat R Sb i k Q α Rr → D.nd.goodRow σ → ∀ y ∈ D.what₂.isot (i.1 + 1) σ,
      EigVec R i k Q Rr (eig (i.1 + 1) σ k Q) (Y.mj.eW i y) := Iff.rfl

theorem EigVec.congr {i : Fin D.R.m} {k : ℕ} {Q : PlE D.host} {Rr : Finset (GA D (Wc D i))} {c : ↥D.LL0}
    {v v' : (R.HW i (sg0 D A3.A)).H} (h : EigVec R i k Q Rr c v) (e : HEq v' v) : EigVec R i k Q Rr c v' := eq_of_heq e ▸ h

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
  {x : St P} (L : LocAll (lay0 (Dof x)))

theorem eigVec_loc {i k Q Rr c v} (h : EigVec x.m.z.R i k Q Rr c v) :
    EigVec (datL x L).R i k Q Rr c v := by
  with_unfolding_all exact h

end GlobalTheory.HeightCounting.Fin3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationGoodRowsToConjugateGoodRowsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_goodRows_to_conjugate_goodRows : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (G : GoodOp X) (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (c : ℝ), R.toLevCh.Is A.μ0 → R.models_inf → (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → SeeAt R F X h t → EvalOn R X h t v₀ c (MultR R F) (conjRows X) → EvalOn R X h t v₀ c (EP R F) (EEC X G) ∧ EvalTieT (MP R) R.ν0 R.fd0 (EP R F) X G (iotaX X h).toMulEquiv t c := by
  first | exact @GlobalTheory.Mem.SRe.evalOn_good | exact GlobalTheory.Mem.SRe.evalOn_good | (intros; apply GlobalTheory.Mem.SRe.evalOn_good <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCopiesReferenceObjectsOverEnlargedBase
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.WeilExt.RefType

private abbrev MM {Tau : Type} {n : ℕ} (H : Tau → Type) (na : ∀ τ, NormedAddCommGroup (H τ)) (ip : ∀ τ, InnerProductSpace ℂ (H τ))
    (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (fr : Tau → Matrix (Fin n) (Fin n) ℂ)
    (lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)) (X : Type) : Type :=
  MultilinearMap (RingHom.id ℂ) (fun τ : Tau => (Submodule.span ℂ {w | SmoothVec (lie τ) (fun g => σ τ (fr τ * g * (fr τ)⁻¹)) w} : Submodule ℂ (H τ)))
    (X → ℂ)

private theorem core {Tau Tau' : Type} {n n' : ℕ} {H : Tau → Type} {na : ∀ τ, NormedAddCommGroup (H τ)} {ip : ∀ τ, InnerProductSpace ℂ (H τ)}
    {σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)} {fr : Tau → Matrix (Fin n) (Fin n) ℂ}
    {lie : Tau → Set (Matrix (Fin n) (Fin n) ℂ)} {X : Type}
    {H' : Tau' → Type} {na' : ∀ τ, NormedAddCommGroup (H' τ)} {ip' : ∀ τ, InnerProductSpace ℂ (H' τ)}
    {σ' : ∀ τ, Matrix (Fin n') (Fin n') ℂ → (H' τ →L[ℂ] H' τ)} {fr' : Tau' → Matrix (Fin n') (Fin n') ℂ}
    {lie' : Tau' → Set (Matrix (Fin n') (Fin n') ℂ)} {X' : Type}
    {G G' C C' : Type} {nc : NormedAddCommGroup C} {ic : InnerProductSpace ℂ C} {nc' : NormedAddCommGroup C'} {ic' : InnerProductSpace ℂ C'}
    {HW : HMod (MM H na ip σ fr lie X)} {HW' : HMod (MM H' na' ip' σ' fr' lie' X')}
    (hT : Tau' = Tau) (hn : n' = n) (hlie : HEq lie' lie) (hX : X' = X) (hG : G' = G)
    (hC : HEq C' C) (hnc : HEq nc' nc) (hic : HEq ic' ic)
    (hH : HEq H' H) (hna : HEq na' na) (hip : HEq ip' ip) (hσ : HEq σ' σ) (hfr : HEq fr' fr) (hHW : HEq HW' HW)
    (K : HMod (G → C)) (th : K.H →ₗ[ℂ] MM H na ip σ fr lie X) (g : K.H →ₗ[ℂ] HW.H) :
    ∃ (K' : HMod (G' → C')) (th' : K'.H →ₗ[ℂ] MM H' na' ip' σ' fr' lie' X') (g' : K'.H →ₗ[ℂ] HW'.H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst hT hn hX hG
  cases hlie; cases hC; cases hnc; cases hic; cases hH; cases hna; cases hip; cases hσ; cases hfr; cases hHW
  exact ⟨K, th, g, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem mid {D D' : D7} {V W : HSp D} {V' W' : HSp D'} {L L' : Type} {S : L → D.what₂.Tau → SPar} {S' : L' → D'.what₂.Tau → SPar}
    (c : CoefA V) (c' : CoefA V') (M : ∀ s, Formalism.IndefR.Mult.DSModel W (S s)) (M' : ∀ s, Formalism.IndefR.Mult.DSModel W' (S' s))
    (HW : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M s))) (HW' : ∀ s, HMod (Formalism.IndefR.Mult.MMap (M' s)))
    {s t : L} {s' t' : L'} (e : t = s) (e' : t' = s')
    (hT : D'.what₂.Tau = D.what₂.Tau) (hn : W'.rank = W.rank) (hlie : HEq (lieAt W') (lieAt W)) (hX : GA D' W' = GA D W)
    (hG : (Bridge.Gf V' : Type) = Bridge.Gf V)
    (hC : HEq c'.W c.W) (hnc : HEq c'.nW c.nW) (hic : HEq c'.iW c.iW)
    (hH : HEq (M' s').H (M s).H) (hna : HEq (M' s').nacg (M s).nacg) (hip : HEq (M' s').ips (M s).ips) (hσ : HEq (M' s').σ (M s).σ)
    (hfr : HEq (M' s').fr (M s).fr) (hHW : HEq (HW' s') (HW s))
    (K : HMod (Bridge.Gf V → c.W)) (th : K.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M t)) (g : K.H →ₗ[ℂ] (HW t).H) :
    ∃ (K' : HMod (Bridge.Gf V' → c'.W)) (th' : K'.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (M' t')) (g' : K'.H →ₗ[ℂ] (HW' t').H),
      HEq K' K ∧ HEq th' th ∧ HEq g' g := by
  subst e e'
  exact core (lie := lieAt W) (lie' := lieAt W') (X := GA D W) (X' := GA D' W') (HW := HW t) (HW' := HW' t')
    hT hn hlie hX hG hC hnc hic hH hna hip hσ hfr hHW K th g

private theorem types (X X' : Stages) (h : X'.B.toPre = X.B.toPre) (i : Fin X.toD7.R.m) (i' : Fin X'.toD7.R.m) (hi : (i : ℕ) = i') :
    X'.toD7.what₂.Tau = X.toD7.what₂.Tau ∧ (Wc X'.toD7 i').rank = (Wc X.toD7 i).rank ∧ HEq (lieAt (Wc X'.toD7 i')) (lieAt (Wc X.toD7 i)) ∧
    GA X'.toD7 (Wc X'.toD7 i') = GA X.toD7 (Wc X.toD7 i) ∧ (Bridge.Gf (Vc X'.toD7 i') : Type) = Bridge.Gf (Vc X.toD7 i) ∧
    (GA X.toD7 (Vc X.toD7 i) × GA X.toD7 (Wc X.toD7 i) →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ)) =
      (GA X'.toD7 (Vc X'.toD7 i') × GA X'.toD7 (Wc X'.toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ)) ∧
    (Formalism.IndefR.Datum.WO (Vc X.toD7 i) (Wc X.toD7 i) → ℂ) = (Formalism.IndefR.Datum.WO (Vc X'.toD7 i') (Wc X'.toD7 i') → ℂ) ∧
    Measure (GA X.toD7 (Vc X.toD7 i)) = Measure (GA X'.toD7 (Vc X'.toD7 i')) ∧
    Set (GA X.toD7 (Vc X.toD7 i)) = Set (GA X'.toD7 (Vc X'.toD7 i')) := by
  obtain ⟨B, C, W, V, S, N, G⟩ := X
  obtain ⟨B', C', W', V', S', N', G'⟩ := X'
  cases B
  cases B'
  dsimp only at h
  subst h
  obtain ⟨i, hlt⟩ := i
  obtain ⟨i', hlt'⟩ := i'
  dsimp only at hi
  subst hi
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

end GlobalTheory.Mem.R3.Rw.WeilExt.RefType

open GlobalTheory.Mem.R3.Rw.WeilExt.RefType in
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_copies_reference_objects_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → RSideW z Wt' R' → ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
  ∃ (ω : GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i') × GA (w'.st Z').toD7 (Wc (w'.st Z').toD7 i') →* Module.End ℂ (Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ))
    (v : Formalism.IndefR.Datum.WO (Vc (w'.st Z').toD7 i') (Wc (w'.st Z').toD7 i') → ℂ) (H : HMod (Bridge.Gf (Vc (w'.st Z').toD7 i') → (R'.cV i').W))
    (th : H.H →ₗ[ℂ] Formalism.IndefR.Mult.MMap (R'.MW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A))) (g : H.H →ₗ[ℂ] (R'.HW i' (sg0 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr).A)).H)
    (ν : Measure (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))) (fd : Set (GA (w'.st Z').toD7 (Vc (w'.st Z').toD7 i'))),
    HEq ω (z.R.ωP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq v (z.R.vP i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq H (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq th (z.R.thF i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧
    HEq g (z.R.thG i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq ν (z.R.νV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) ∧ HEq fd (z.R.fdV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hR i i' hi
  have hR' := hR.2.2.2.2.2.2.2.2.2.2.2.2.1 i i' hi
  obtain ⟨hC, -, hnc, hic, -, -, -, hH, hna, hip, hσ, -, -, hfr, -, hHW, -⟩ := hR'
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9⟩ := types (w.st Z) (w'.st Z') hE.1 i i' hi
  have key := mid (z.R.cV i) (R'.cV i') (z.R.MW i) (R'.MW i') (z.R.HW i) (R'.HW i')
    (sgAt_mk _ z.R.hv0) (sgAt_mk _ R'.hv0) t1 t2 t3 t4 t5 hC hnc hic hH hna hip hσ hfr hHW
    (z.R.HV i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))) (z.R.thF i _) (z.R.thG i _)
  obtain ⟨K, th, g, h1, h2, h3⟩ := key
  exact ⟨cast t6 (z.R.ωP i _), cast t7 (z.R.vP i _), K, th, g, cast t8 (z.R.νV i _), cast t9 (z.R.fdV i _), cast_heq _ _, cast_heq _ _,
    h1, h2, h3, cast_heq _ _, cast_heq _ _⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocal
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

open Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_divX (Z : RationalReadingWithoutCongruence R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : Nonempty (DivX D) := by
  obtain ⟨G, V, -⟩ := GlobalTheory.PointGeometry.exists_geo D.what₂.LL
  exact ⟨GlobalTheory.provisionalDivX D G V (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) fun k =>
    ⟨mjH_noEta Z k, jM_noEta Z k, mjH_good_noEta Z hH k, jM_basis_noEta Z hH k, jM_lat_noEta Z hP hH k,
      mjLat_sub_noEta Z hP hH k, MjModel.jM_metric_all_noEta Z hH k⟩⟩

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.A.fam.base.Ix := by
  obtain ⟨p⟩ := GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ (hH.ok.ok2.what₂ A3.A.μ0).comm p.2⟩

end GlobalTheory.HeightCounting.Up.ThirdIdx

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

end GlobalTheory.HeightCounting.Up.ThirdIdx

end
end

