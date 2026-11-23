module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0078
public import Formalism.LocalToGlobal.KernelLattices.ThDistC

@[expose] public section

noncomputable section

namespace GlobalTheory.GO

open NumberField _root_.Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.Ker

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure MemOn (F : GFam K) where

  G : Type
  [grpG : Group G]

  D : Type
  [actD : MulAction G D]

  ρ : G →* Module.End K F.V

  Nab : D → Submodule (𝓞 K) F.V

  Del : D → Submodule (𝓞 K) F.V

attribute [instance] MemOn.grpG MemOn.actD

@[reducible] def MemOn.gsd {F : GFam K} (M : MemOn F) : GSD K where
  G := M.G
  D := M.D
  V := F.V
  ιV := F.ιV
  bV := F.bV
  pair := F.pair
  ρ := M.ρ
  Nab := M.Nab
  Del := M.Del

@[reducible] def MemOn.self (F : GFam K) (b : F.β) : MemOn F where
  G := F.G b
  D := F.D b
  ρ := F.ρ b
  Nab := F.Nab b
  Del := F.Del b

@[reducible] def MemOn.pairs (F : GFam K) (b : F.β) (Y : Cpl (F.mem b)) : MemOn F where
  G := F.G b
  D := Y.Pts
  actD := (cplGSD (F.mem b) Y).actD
  ρ := F.ρ b
  Nab d := F.Nab b d.1.1
  Del d := F.Del b d.1.1

inductive SpIdx (β : ℕ → Type) (n m i : ℕ) : Type
  | mat (b : β i) (h : i ≤ n) : SpIdx β n m i
  | cpl (h : i = n + 1) : SpIdx β n m i
  | top (h : i = m) : SpIdx β n m i

namespace SpIdx

variable {β : ℕ → Type} {n m i : ℕ}

instance [Finite (β i)] : Finite (SpIdx β n m i) :=
  Finite.of_injective (fun b : SpIdx β n m i => match b with
    | .mat b _ => (Sum.inl b : β i ⊕ Bool)
    | .cpl _ => Sum.inr false
    | .top _ => Sum.inr true) (by
      rintro (⟨a, _⟩ | _ | _) (⟨b, _⟩ | _ | _) h <;> simp_all)

instance [Finite (β i)] : Fintype (SpIdx β n m i) := Fintype.ofFinite _

instance : DecidableEq (SpIdx β n m i) := Classical.decEq _

theorem isEmpty_of_lt (hm : n + 1 < m) (h : m < i) : IsEmpty (SpIdx β n m i) :=
  ⟨fun b => by rcases b with ⟨_, h'⟩ | h' | h' <;> omega⟩

end SpIdx

section Splice

variable (F : ℕ → GFam K) (n m : ℕ) (C : MemOn (F (n + 1))) (T : MemOn (F m))

@[reducible] def spMem : ∀ (i : ℕ) (_ : SpIdx (fun j => (F j).β) n m i), MemOn (F i)
  | i, .mat b _ => MemOn.self (F i) b
  | _, .cpl rfl => C
  | _, .top rfl => T

@[reducible] def spFam (i : ℕ) : GFam K where
  β := SpIdx (fun j => (F j).β) n m i
  V := (F i).V
  ιV := (F i).ιV
  bV := (F i).bV
  pair := (F i).pair
  G b := (spMem F n m C T i b).G
  D b := (spMem F n m C T i b).D
  ρ b := (spMem F n m C T i b).ρ
  Nab b := (spMem F n m C T i b).Nab
  Del b := (spMem F n m C T i b).Del

variable {F n m C T}

theorem spFam_ok (hF : ∀ i, i ≤ n → (F i).Ok) (hC : C.gsd.Ok) (hT : T.gsd.Ok) (i : ℕ) : (spFam F n m C T i).Ok := by
  rintro (⟨b, h⟩ | rfl | rfl)
  · exact hF i h b
  · exact hC
  · exact hT

def spEntry (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)
    (i j : ℕ) (e : j = i + 1) : ∀ (b : (spFam F n m C T i).β) (b' : (spFam F n m C T j).β),
      ClsKer ((spFam F n m C T i).mem b) ((spFam F n m C T j).mem b')
  | .mat al _, .mat be _ => (match j, e, be with | _, rfl, be => kk i al be : ClsKer ((F i).mem al) ((F j).mem be))
  | .mat al _, .cpl h' =>
    (match i, j, (Nat.succ.inj (h'.symm.trans e) : n = i), h', al with | _, _, rfl, rfl, al => k1 al :
      ClsKer ((F i).mem al) ((spFam F n m C T j).mem (.cpl h')))
  | .cpl h, .top h' =>
    (match i, j, h, h' with | _, _, rfl, rfl => k2 :
      ClsKer ((spFam F n m C T i).mem (.cpl h)) ((spFam F n m C T j).mem (.top h')))
  | .mat _ _, .top _ => zeroKer _ _
  | .cpl _, .mat _ _ => zeroKer _ _
  | .cpl _, .cpl _ => zeroKer _ _
  | .top _, _ => zeroKer _ _

variable (kk : KerFam F) (k1 : ∀ al : (F n).β, ClsKer ((F n).mem al) C.gsd) (k2 : ClsKer C.gsd T.gsd)

def spKer : KerFam (spFam F n m C T) := fun i b b' => spEntry kk k1 k2 i (i + 1) rfl b b'


variable {hS : ∀ i, (spFam F n m C T i).Ok}

end Splice

end GlobalTheory.GO
