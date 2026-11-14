{ config, ... }: {
  key = "K";
  __keyEq = if config.a == 0 then null else null;
}
