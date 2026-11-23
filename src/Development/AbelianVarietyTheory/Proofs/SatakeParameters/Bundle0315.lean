module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.GramLevelZeroEqReindex
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0019
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.RealStructures.Imports
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.ImportsBis
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChTwDGamDvdMemDGam
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem chTw_DGam_dvd_mem_DGam : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup), (D.chTw u μ).DGam ∣ (D.mem u).C.DGam := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ
  exact (ex.err.dgam.one u u μ).dvd

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChiRatAllOfAdTie
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwUChiRat

open GlobalTheory.TwU Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG NumberField IsDedekindDomain

section Gen

variable {D : D7} {X : Fields} (s : Seam D X) {i : ℕ} {hi : i ≤ D.R.m} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T D.R.f bad) {SB : Finset (HeightOneSpectrum (𝓞 X.E))}
  (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)
  (Rel : SB → (Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)) → X.K → Prop)

theorem exists_isOver (Q : HeightOneSpectrum (𝓞 D.host.E)) : ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v Q := by
  refine ⟨⟨Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _, ?_⟩, rfl⟩
  intro h
  have hN : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 D.host.F) ∈ Q.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact Ideal.absNorm_mem _
  rw [h, Ideal.mem_bot] at hN
  have : Ideal.absNorm Q.asIdeal = 0 := by exact_mod_cast hN
  exact Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 this)

theorem chiRatAll_of_le (hLe : LocLe s lev fb dep Rel) (hChi : ChiIs s lev fb dep Rel)
    (hK : ∀ y : X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = s.σ₀ y) : ChiRatAll lev D.what₂.embLL := by
  classical
  intro κ
  have hv : ∀ P : SB, ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP s P.1) := fun P => exists_isOver (seamP s P.1)
  choose v hv using hv
  have hU := (lev.U_eq κ.1).1 κ.2
  have hgz : ∀ P : SB, ∃ g z, Rel P g z ∧ InFrame s fb dep P κ.1 g := fun P => hLe P (v P) (hv P) κ.1 hU.1 (hU.2 (v P))
  choose g z hgz using hgz
  have h1 := hChi κ g z hgz
  obtain ⟨k, hk⟩ := hK (∏ P, z P)
  refine ⟨k⁻¹, ?_⟩
  rw [map_inv₀, hk]
  exact (eq_inv_of_mul_eq_one_left h1).symm

end Gen

theorem chiRatAll_of_adTie : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ) (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (a : 𝓞 D.host.E), GlobalTheory.TwU.AdTie A dtU a → (∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y) → ∀ i hi β, ChiRatAll ((St i hi).K β).lev D.what₂.embLL := by
  intro D L hT Gi Gl Kc Dx cX ex t u μ St A dtU a H hK i hi β
  have hm := m_eq t μ
  rcases Nat.lt_or_ge t.m2 i with h | h
  · rcases Nat.lt_or_ge (t.m2 + 1) i with h' | h'
    · obtain rfl : i = t.m2 + 1 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levTop β).1 (H.levTop β).2 hK
    · obtain rfl : i = t.m2 + 1 := by omega
      exact chiRatAll_of_le t.seam _ _ _ _ (H.levCpl β).1 (H.levCpl β).2.2 hK
  · have hlt : i < D.R.m := by omega
    exact chiRatAll_of_le t.seam _ _ _ _ (H.levMid i hlt h β).1 (H.levMid i hlt h β).2.2 hK

end GlobalTheory.TwUChiRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPlaceNormVEq
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.PlaceNormDec

theorem exists_place_normV_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w → Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range → ∃ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w ∧ IsPlaceOver A w' ∧ normV w' = normV w := by
  intro E Ω _ _ _ _ _ Q w A hA hD
  obtain ⟨w', hw', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω (↥Q.K) w A hA hD
  refine ⟨w', ?_, hw', ?_⟩
  · have hl := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA hw'
    exact HeightOneSpectrum.ext hl.over.symm
  · obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA (↥Q.K) Ω A w' hw' (RingEquiv.refl Ω) (algebraMap E ↥Q.K) i hi
    exact hq

end GlobalTheory.PlaceNormDec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HServTwoSidesJoint0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.hServTwoSidesJoint0 : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (C : ColsTiedSym D) (full : ColsFullS C), g.herm = full.1.to0 → (g.forms = fun u => (C.forms u).to0) → ∀ u, Joint0 g.herm.lev0 u (g.forms u) := by
  intro D Gt c g C full hh hf u
  rw [hh, hf]
  have e : full.1.to0.lev0 = C.herm.base.lev0 :=
    congrArg (fun X : Formalism.L2.Herm.ColsHermS D => X.base.lev0) full.2
  rw [e]
  exact C.joint0 u
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemUnderSBOfGIdx
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwU

theorem not_mem_underSB_of_gIdx : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Dx cX} (t : KerEntTied ex) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (μ : D.what₂.Tup), (D.what₂.places.resChar w) ∉ Dx.Qp μ → ∀ v, GlobalTheory.TwU.UnderSB t μ v → ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
  intro D L hT Gi Gl Kc Dx cX ex t u w hg μ hQ v hv hmem
  classical
  obtain ⟨P, hP, hvP⟩ := hv
  have h1 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P).asIdeal := by
    have h0 : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈
        (seamP t.seam P).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hvP ▸ hmem
    rw [Ideal.mem_comap, map_natCast] at h0
    exact h0
  have h2 : ((D.what₂.places.resChar w : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
    rw [← mem_seamP t.seam P, map_natCast]
    exact h1
  rcases Finset.mem_union.1 hP with hG | hQE
  · obtain ⟨k, hk⟩ : ∃ k, P ∈ t.Pr.vG k := by
      rcases Finset.mem_union.1 hG with h | h
      exacts [⟨0, h⟩, ⟨1, h⟩]
    have hgk : ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.pr_ok.vG_norm k P hk]
      exact Ideal.absNorm_mem P.asIdeal
    have hnd : ¬ D.what₂.places.resChar w ∣ t.Pr.g k := by
      rw [t.g_rec]
      intro hd
      exact hg.2.2.2.2.1 (((Nat.prime_dvd_prime_iff_eq hg.1 (D.host.g_prime k)).1 hd) ▸ D.host.g_level k)
    have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : ℤ) ((t.Pr.g k : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hg.1).2 hnd)
    obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 t.X.E))
    have hone : (1 : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← hab]
      refine P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ ?_) (P.asIdeal.mul_mem_left _ ?_)
      · simpa using h2
      · simpa using hgk
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hone)
  · exact hQ ((t.Q_rec μ _).2 ⟨hg.1, P, hQE, h2⟩)

end GlobalTheory.TwU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplAlgLocAt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.CmpJ.AgreeLv Formalism.MainNotions.G.KAat Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.LbB

section Inst

variable {D : D7} {X : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}

theorem locInt_locAt (B : GL (Fin D.R.k) D.host.E) : LocInt (locAt X u w hg B) := by
  intro v x
  exact (X.g u w hg).completion_integers_iff v _ rfl x

theorem splAlg_locAt (B : GL (Fin D.R.k) D.host.E) : GlobalTheory.TwV.SplAlg (locAt X u w hg B) := by
  intro v a
  exact (X.g u w hg).spl_alg _ _ a

theorem reL_eq_map {a b : ℕ} (h : a = b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) :
    reL h L = L.map (((Formalism.L2.PairingIndexBounds.F.reE (E := D.host.E) h : (Fin a → D.host.E) ≃ₗ[D.host.E] (Fin b → D.host.E)) :
      (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E)).restrictScalars (𝓞 D.host.E)) := by
  subst h
  rfl


set_option maxHeartbeats 400000 in
theorem lbAtB_locAt (B : GL (Fin D.R.k) D.host.E) (hrat : FrRat X u w hg B) (L : Submodule (𝓞 D.host.E) (Fin (D.R.N 0) → D.host.E))
    (hL : L = reL (rank_eq_first_level D.R) (X.lev0 u).Lb) : GlobalTheory.TwV.LbAtB (locAt X u w hg B) L := by
  rw [hL, reL_eq_map]
  exact lbAtB_of _ (locInt_locAt B) (splAlg_locAt B) _
    (frAtB_re (rank_eq_first_level D.R) (locAt X u w hg B) (X.lev0 u).Lb B rfl (fun v => (X.g u w hg).fr _ ((X.g u w hg).pl v).2)
      (fun v tt => (X.g u w hg).fr_lat _ _ tt) (fun v => hrat _ _))

end Inst

theorem lbAtB_lev0At : ∀ {D : D7} (Gt : GatTies D) (c : LatCmp D) (g : GroupCompatibilityAll D Gt c) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), Joint0 g.herm.lev0 u (g.forms u) → GlobalTheory.TwV.LbAtB (lev0At g u w hg).A (lev0At g u w hg).Lb := by
  intro D Gt c g u w hg hJ
  exact lbAtB_locAt g.cmp.B (g.cmp.fr_B u w hg) _ hJ.Lb_eq

end GlobalTheory.TwV.LbB

end
end

