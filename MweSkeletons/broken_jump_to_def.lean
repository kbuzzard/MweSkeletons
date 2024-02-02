import MweSkeletons.CommRing -- includes a new definition of CommRing independent of mathlib

#check CommRing -- hover says `import MweSkeletons.CommRing`
-- but "jump to definition" and "jump to declaration" both jump to mathlib
-- despite no mathlib files being imported here.
